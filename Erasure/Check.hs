{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}

module Erasure.Check (check, instantiate, TCFailure) where

import TT
import TTLens
import TTUtils
import Normalise
import Erasure.Meta
import Erasure.Solve

import Prelude hiding (lookup)

import Data.Maybe
import Data.Foldable
import Control.Monad
import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

import Lens.Family

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

import Debug.Trace

data TCError
    = CantConvert TTmeta TTmeta
    | Mismatch String String
    | UnknownName Name
    | WrongType TTmeta TTmeta  -- term, type
    | BadCtorType TTmeta
    | NonFunction TTmeta TTmeta  -- term, type
    | EmptyCaseTree TTmeta
    | CantMatch TTmeta TTmeta
    | NonVariableScrutinee TTmeta
    | InconsistentErasure Name
    | NotImplemented String
    | Other String
    deriving (Eq, Ord, Show)

data TCFailure = TCFailure TCError [String]

instance Show TCFailure where
    show (TCFailure e []) = show e
    show (TCFailure e tb) = unlines $
        show e : "Traceback:"
            : zipWith
                (\i n -> show i ++ ". " ++ n)
                [1..]
                (reverse tb)

type TCTraceback = [String]
type TCState = Int
type TC a = ReaderT (TCTraceback, Ctx Meta Constrs') (ExceptT TCFailure (State TCState)) a
type Sig = (Meta, Type, Constrs)  -- relevance, type, constraints

type Term = TT Meta
type Type = TT Meta

infixl 2 /\
(/\) :: Constrs -> Constrs -> Constrs
(/\) = union

infix 3 -->
(-->) :: Meta -> Meta -> Constrs
g --> u = CS $ M.singleton (S.singleton g) (S.singleton u)

infix 3 <-->
(<-->) :: Meta -> Meta -> Constrs
p <--> q = p --> q /\ q --> p

eq :: Meta -> Meta -> Constrs
eq p q = p <--> q

union :: Constrs -> Constrs -> Constrs
union (CS x) (CS y) = CS $ M.unionWith S.union x y

unions :: [Constrs] -> Constrs
unions = CS . M.unionsWith S.union . map runCS

noConstrs :: Constrs
noConstrs = CS M.empty

-- newtype Constrs' r = CS { runCS :: M.Map (Guards' r) (Uses' r) }
flipConstrs :: Constrs -> Constrs
flipConstrs (CS cs)
    = unions
        [ p --> q
        | (qs, ps) <- M.toList cs
        , q <- S.toList qs
        , p <- S.toList ps
        ]

cond :: Meta -> Constrs -> Constrs
cond r = CS . M.mapKeysWith S.union (S.insert r) . runCS

with :: Def Meta Constrs' -> TC a -> TC a
with d@(Def n r ty mtm mcs) = with' $ M.insert n d

with' :: (Ctx Meta Constrs' -> Ctx Meta Constrs') -> TC a -> TC a
with' f = local $ \(tb, ctx) -> (tb, f ctx)

bt :: Show a => a -> TC b -> TC b
bt dbg sub = do
    ctx <- getCtx
    let btLine = "In context:\n" ++ showCtx ctx ++ "\n" ++ show dbg ++ "\n"
    local (\(tb,ctx) -> (btLine:tb,ctx)) sub

showCtx :: Ctx Meta Constrs' -> String
showCtx ctx = unlines
    [ "  " ++ show n ++ " : " ++ show ty
    | (n, Def _n _r ty _mtm _mcs) <- M.toList ctx
    ]

tcfail :: TCError -> TC a
tcfail e = do
    (tb, ctx) <- ask
    lift . throwE $ TCFailure e tb

getCtx :: TC (Ctx Meta Constrs')
getCtx = do
    (tb, ctx) <- ask
    return ctx

require :: Bool -> TCError -> TC ()
require True  e = return ()
require False e = tcfail e

lookup :: Name -> TC (Def Meta Constrs')
lookup n = do
    ctx <- getCtx
    case M.lookup n ctx of
        Just x  -> return x
        Nothing -> tcfail $ UnknownName n

freshTag :: TC Int
freshTag = lift $ lift (modify (+1) >> get)

runTC :: Int -> Ctx Meta Constrs' -> TC a -> Either TCFailure a
runTC maxTag ctx tc = evalState (runExceptT $ runReaderT tc ([], ctx)) maxTag

check :: Program Meta VoidConstrs -> Either TCFailure (Ctx Meta Constrs')
check prog@(Prog defs) = runTC maxTag ctx $ checkDefs defs
  where
    getTag (MVar i) = i
    getTag _        = 0  -- whatever, we're looking for maximum

    allTags = prog ^.. progRelevance . to getTag
    maxTag = L.maximum allTags

    ctx = builtins (Fixed R)

checkDefs :: [Def Meta VoidConstrs] -> TC (Ctx Meta Constrs')
checkDefs [] = getCtx
checkDefs (d:ds) = do
    d' <- with (csDef d) $ checkDef d
    let d'' = d'{ defConstraints = reduce <$> defConstraints d' }
    with d'' $ checkDefs ds

checkDef :: Def Meta VoidConstrs -> TC (Def Meta Constrs')

checkDef (Def n r ty (Abstract a) Nothing) = do
    (tyty, tycs) <- checkTm ty
    tytyTypeCs <- conv tyty (V $ UN "Type")
    let cs = tycs /\ tytyTypeCs /\ Fixed R --> r
    return $ Def n r ty (Abstract a) (Just $ cond r cs)

checkDef (Def n r ty (Term tm) Nothing) = bt ("DEF-TERM", n) $ do
    (tmty, tmcs) <- checkTm tm
    (tyty, tycs) <- checkTm ty
    tytyTypeCs   <- conv tyty (V $ UN "Type")
    tyTmtyCs     <- conv ty tmty
    let cs = tmcs /\ tycs /\ tytyTypeCs /\ tyTmtyCs /\ Fixed R --> r
    return $ Def n r ty (Term tm) (Just $ cond r cs)

checkDef (Def n r ty (Patterns cf) Nothing) = bt ("DEF-PATTERNS", n) $ do
    (tyty, tycs) <- checkTm ty
    tytyTypeCs   <- conv tyty (V $ UN "Type")
    cfCs <- checkCaseFun n cf
    let cs = tycs /\ tytyTypeCs /\ cfCs /\ Fixed R --> r
    return $ Def n r ty (Patterns cf) (Just $ cond r cs)

checkCaseFun :: Name -> CaseFun Meta -> TC Constrs
checkCaseFun fn (CaseFun args ct) = bt ("CASE-FUN", fn) $ do
    argCtx <- checkDefs args
    with' (M.union argCtx)
        $ checkCaseTree lhs ct
  where
    lhs = mkApp (V fn) [(r, V n) | Def n r ty (Abstract Var) Nothing <- args]

checkCaseTree :: TT Meta -> CaseTree Meta -> TC Constrs
checkCaseTree lhs (Leaf rhs) = bt ("PLAIN-TERM", lhs, rhs) $ do
    (lty, lcs) <- checkTm lhs
    (rty, rcs) <- checkTm rhs
    ccs <- conv lty rty
    return $ flipConstrs lcs /\ rcs /\ ccs

checkCaseTree lhs ct@(Case r (V n) alts) = bt ("CASE", lhs, ct) $ do
    nr <- defR <$> lookup n
    cs <- unions <$> traverse (checkAlt isSingleBranch lhs n r) alts
    return $ cs /\ r --> nr /\ scrutineeCs
  where
    scrutineeCs
        | isSingleBranch = noConstrs
        | otherwise      = Fixed R --> r

    isSingleBranch
        | [_] <- alts = True
        | otherwise   = False

checkCaseTree lhs (Case r s alts) =
    tcfail $ NonVariableScrutinee s


checkAlt :: Bool -> TT Meta -> Name -> Meta -> Alt Meta -> TC Constrs

checkAlt isSingleBranch lhs n sr (Alt Wildcard rhs) = bt ("ALT-WILDCARD") $ do
    checkCaseTree lhs rhs

checkAlt isSingleBranch lhs n sr (Alt (Ctor cn args eqs_NF) rhs) = bt ("ALT-CTOR", pat) $ do
    argCtx <- checkDefs args
    -- Typechecking will be done eventually in the case for Leaf.
    cs <- with' (M.union argCtx) $
            with' (substsInCtx eqs') $  -- substitutes in args, too; must use eqs', which includes (n, pat')
                checkCaseTree lhs' rhs'
    return $ cs /\ scrutCs
  where
    ctor
        | isSingleBranch = Forced (V cn)
        | otherwise      = V cn

    eqs = [(n, Forced tm) | (n, tm) <- eqs_NF]

    -- don't forget to rewrite in pat!
    pat = mkApp ctor [(r, V n) | Def n r ty (Abstract Var) Nothing <- args]
    pat' = substs eqs pat

    eqs' = (n, pat') : eqs
    lhs' = substs eqs' lhs
    rhs' = substs eqs' rhs

    -- bindings from the individual vars to the scrutinee
    scrutCs = unions [defR d --> sr | d <- args]


withDefs :: [Def Meta Constrs'] -> TC a -> TC a
withDefs (Def n r ty body cs : ds) = with (Def n r ty body cs) . withDefs ds
withDefs [] = id

checkTm :: Term -> TC (Type, Constrs)

-- this is sketchy
checkTm (V Blank) = return (V Blank, noConstrs)

checkTm t@(V n) = bt ("VAR", n) $ do
    -- at the point of usage of a bound name,
    -- the constraints associated with that name come in
    d <- lookup n
    return (defType d, defConstraints d)

checkTm t@(I n ty) = bt ("INST", n, ty) $ do
    -- here, we need to freshen the constraints before bringing them up
    d <- instantiate freshTag IM.empty =<< lookup n
    convCs <- conv (defType d) ty
    -- This (Fixed R --> r) thing is tricky.
    --
    -- We should not include (Fixed R --> r) because it will be an instance
    -- of this function that's runtime-relevant, not the function itself.
    --
    -- However, we must mark the instance as runtime-relevant, but it does not
    -- exist yet. Hence we mark the original function as runtime-relevant as a proxy
    -- for the relevance of the instance, and all instances will inherit this relevance.
    --
    -- In the next iteration of typechecking after specialisation,
    -- the original function will be recognised as erased again, if necessary.
    --
    -- Also, all unused instances should be recognised as erased (I didn't check that).
    return (ty', defConstraints d /\ convCs)

checkTm t@(Bind Lam d@(Def n r ty (Abstract Var) Nothing) tm) = bt ("LAM", t) $ do
    d' <- checkDef d
    (tmty, tmcs) <- with d' $ checkTm tm
    return (Bind Pi (csDef d') tmty, tmcs)

checkTm t@(Bind Pi d@(Def n r ty (Abstract Var) Nothing) tm) = bt ("PI", t) $ do
    d' <- checkDef d
    (tmty, tmcs) <- with d' $ checkTm tm
    return (V $ UN "Type", tmcs)

checkTm t@(App app_r f x) = bt ("APP", t) $ do
    (fty, fcs) <- checkTm f
    (xty, xcs) <- checkTm x
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi (Def n' pi_r ty' (Abstract Var) Nothing) retTy -> do
            tycs <- conv xty ty'
            let cs =
                    tycs
                    /\ fcs
                    /\ cond pi_r xcs
                    /\ pi_r <--> app_r
            return (subst n' x retTy, cs)

        _ -> do
            tcfail $ NonFunction f fty

checkTm t@(Bind Let d tm) = bt ("LET", t) $ do
    (ds, dcs) <- checkDefs noConstrs [d]
    (tmty, tmcs) <- withDefs (M.elems ds) $ checkTm tm
    return (tmty, dcs /\ tmcs)

checkTm (Forced tm) = bt ("FORCED", tm) $ do
    (ty, _cs) <- checkTm tm
    return (ty, noConstrs)

newtype TC' a = LiftTC' { runTC' :: TC a } deriving (Functor, Applicative, Monad)
type ITC = StateT (IM.IntMap Int) TC'

freshen :: Monad m => m Int -> Meta -> StateT (IM.IntMap Meta) m Meta
freshen freshTag m@(Fixed r) = return m
freshen freshTag (MVar i) = do
    imap <- get
    case IM.lookup i imap of
        Just j ->
            return j
        Nothing -> do
            j <- MVar <$> lift freshTag
            modify $ IM.insert i j
            return j

instantiate :: (Functor m, Monad m, CsRelevance cs) => m Int -> IM.IntMap Meta -> Def Meta cs -> m (Def Meta cs)
instantiate freshTag metaMap def = evalStateT refresh metaMap
  where
    refresh = defRelevance' csRelevance (freshen freshTag) def

-- left: from context (from outside), right: from expression (from inside)
conv :: Type -> Type -> TC Constrs
conv p q = do
    ctx <- getCtx
    conv' (whnf ctx p) (whnf ctx q)

-- note that this function gets arguments in WHNF
conv' :: Type -> Type -> TC Constrs

-- whnf is variable (something irreducible, constructor or axiom)
conv' (V n) (V n') = bt ("C-VAR", n, n') $ do
    require (n == n') $ Mismatch (show n) (show n')
    return noConstrs

conv' p@(Bind b (Def n r ty (Abstract Var) Nothing) tm) q@(Bind b' (Def n' r' ty' (Abstract Var) Nothing) tm')
    = bt ("C-BIND", p, q) $ do
        require (b == b') $ Mismatch (show b) (show b')
        xs <- conv ty (rename n' n ty')
        ys <- with (Def n r ty (Abstract Var) Nothing) $ conv tm (rename n' n tm')
        return $ xs /\ ys /\ r <--> r'

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    xs <- conv f f'
    ys <- conv x x'
    return $ xs /\ ys /\ r <--> r'

-- we don't include a case for Forced because those constructors
-- get normalised away to bare terms

conv' p q = tcfail $ CantConvert p q
