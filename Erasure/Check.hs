{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}

module Erasure.Check (check, instantiate, unions, TCFailure) where

import TT
import TTLens
import TTUtils
import Normalise
import Erasure.Meta
import Erasure.Solve

import Prelude hiding (lookup)
import Control.Monad (when)

import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader

import Lens.Family2

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

--import Debug.Trace

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
    | NotConstructor Name
    | InconsistentErasure Name
    | NotImplemented String
    | NonPatvarInEq Name
    | UncheckableTerm TTmeta
    | Other String
    deriving (Eq, Ord, Show)

data TCFailure = TCFailure TCError [String]

instance Show TCFailure where
    show (TCFailure e []) = show e
    show (TCFailure e tb) = unlines $
            "Traceback:"
            : zipWith
                (\i n -> show i ++ ". " ++ n)
                [1::Integer ..]
                (reverse tb)
            ++ ["Error: " ++ show e]

type TCTraceback = [String]
type TCState = Int
type TC a = ReaderT (TCTraceback, Ctx Meta) (ExceptT TCFailure (State TCState)) a

type Term = TT Meta
type Type = TT Meta

infixl 2 /\
(/\) :: Constrs Meta -> Constrs Meta -> Constrs Meta
(/\) = union

infix 3 -->
(-->) :: Meta -> Meta -> Constrs Meta
g --> u = M.singleton (S.singleton g) (S.singleton u)

infix 3 <-->
(<-->) :: Meta -> Meta -> Constrs Meta
p <--> q = p --> q /\ q --> p

union :: Constrs Meta -> Constrs Meta -> Constrs Meta
union = M.unionWith S.union

unions :: [Constrs Meta] -> Constrs Meta
unions = M.unionsWith S.union

-- newtype Constrs' r = CS { runCS :: M.Map (Guards' r) (Uses' r) }
flipConstrs :: Constrs Meta -> Constrs Meta
flipConstrs cs
    = unions
        [ p --> q
        | (qs, ps) <- M.toList cs
        , q <- S.toList qs
        , p <- S.toList (ps `S.difference` S.singleton (Fixed R))
        ]

cond :: Meta -> Constrs Meta -> Constrs Meta
cond r = M.mapKeysWith S.union (S.insert r)

with :: Def Meta -> TC a -> TC a
with d = with' $ M.insert (defName d) d

{-
withs :: [Def Meta] -> TC a -> TC a
withs []     = id
withs (d:ds) = with d . withs ds
-}

with' :: (Ctx Meta -> Ctx Meta) -> TC a -> TC a
with' f = local $ \(tb, ctx) -> (tb, f ctx)

bt :: Show a => a -> TC b -> TC b
bt dbg sub = do
    ctx <- getCtx
    let btLine = "In context:\n" ++ showCtx ctx ++ "\n" ++ show dbg ++ "\n"
    local (\(tb,ctx) -> (btLine:tb,ctx)) sub

showCtx :: Ctx Meta -> String
showCtx ctx = unlines
    [ "  " ++ show (defName d) ++ " : " ++ show (defType d)
    | d <- M.elems ctx
    ]

tcfail :: TCError -> TC a
tcfail e = do
    (tb, ctx) <- ask
    lift . throwE $ TCFailure e tb

getCtx :: TC (Ctx Meta)
getCtx = do
    (tb, ctx) <- ask
    return ctx

require :: Bool -> TCError -> TC ()
require True  e = return ()
require False e = tcfail e

lookup :: Name -> TC (Def Meta)
lookup n = do
    ctx <- getCtx
    case M.lookup n ctx of
        Just x  -> return x
        Nothing -> tcfail $ UnknownName n

freshTag :: TC Int
freshTag = lift $ lift (modify (+1) >> get)

runTC :: Int -> Ctx Meta -> TC a -> Either TCFailure a
runTC maxTag ctx tc = evalState (runExceptT $ runReaderT tc ([], ctx)) maxTag

check :: Program Meta -> Either TCFailure (Constrs Meta)
check prog = runTC maxTag ctx $ do
    (_ty, cs) <- checkTm prog
    return cs
  where
    getTag :: Meta -> Int
    getTag (MVar i) = i
    getTag _        = 0  -- whatever, we're looking for maximum

    allTags :: [Int]
    allTags = map getTag (prog ^.. (ttRelevance :: Traversal' (Program Meta) Meta))

    maxTag = L.maximum allTags

    ctx = builtins (Fixed relOfType)

checkDefs :: [Def Meta] -> TC (Ctx Meta)
checkDefs [] = getCtx
checkDefs (d:ds) = do
    d' <- with d $ checkDef d
    let d'' = d'{ defConstraints = reduce $ defConstraints d' }
    with d'' $ checkDefs ds

checkDef :: Def Meta -> TC (Def Meta)
-- In types, only conversion constraints matter but they *do* matter.
-- We should probably explain on an example why.
--
-- The point is that the conversion check binds the type signature (the asserted type)
-- with the inferred type, also binding the metavars in them, so that the signature
-- can later represent the whole definition.

checkDef (Def n r ty (Abstract a) _noCs) = do
    (tyty, tycs) <- checkTm ty
    tytyTypeCs <- conv tyty (V $ UN "Type")
    let cs = tytyTypeCs  -- in types, only conversion constraints matter
    return $ Def n r ty (Abstract a) cs

checkDef d@(Def n r ty (Term tm) _noCs) = bt ("DEF-TERM", n) $ do
    (tmty, tmcs) <- with d $ checkTm tm  -- "with d" because it could be recursive
    (tyty, tycs) <- checkTm ty
    tytyTypeCs   <- conv tyty (V $ UN "Type")
    tyTmtyCs     <- conv ty tmty
    let cs = tmcs /\ tytyTypeCs /\ tyTmtyCs  -- in types, only conversion constraints matter
    return $ Def n r ty (Term tm) cs

checkDef d@(Def n r ty (Patterns cf) _noCs) = bt ("DEF-PATTERNS", n) $ do
    (tyty, tycs) <- checkTm ty
    tytyTypeCs   <- conv tyty (V $ UN "Type")
    cfCs <- with d $ checkCaseFun n cf  -- "with d" because it could be recursive
    let cs = tytyTypeCs /\ cfCs  -- in types, only conversion constraints matter
    return $ Def n r ty (Patterns cf) cs

checkCaseFun :: Name -> CaseFun Meta -> TC (Constrs Meta)
checkCaseFun fn (CaseFun args ct) = bt ("CASE-FUN", fn) $ do
    argCtx <- checkDefs args
    with' (M.union argCtx)
        $ checkCaseTree lhs ct
  where
    lhs = mkApp (V fn) [(r, V n) | Def n r ty (Abstract Var) cs <- args]

checkCaseTree :: TT Meta -> CaseTree Meta -> TC (Constrs Meta)
checkCaseTree lhs (Leaf rhs) = bt ("PLAIN-TERM", lhs, rhs) $ do
    (lty, lcs) <- checkTm lhs
    (rty, rcs) <- checkTm rhs
    ccs <- conv lty rty
    return $ flipConstrs lcs /\ rcs /\ ccs

checkCaseTree lhs ct@(Case r (V n) alts) = bt ("CASE", lhs, ct) $ do
    checkPatvar n
    nr <- defR <$> lookup n
    cs <- unions <$> traverse (checkAlt lhs n r) alts
    return $ cs /\ r --> nr /\ scrutineeCs
  where
    scrutineeCs = case alts of
        [] -> noConstrs
        _  -> Fixed R --> r

checkCaseTree lhs (Case r s alts) =
    tcfail $ NonVariableScrutinee s


checkPatvar :: Name -> TC ()
checkPatvar n = do
    d <- lookup n
    case d of
        Def n r ty (Abstract Var) cs
            -> return ()
        _
            -> tcfail $ NonPatvarInEq n


checkAlt :: TT Meta -> Name -> Meta -> Alt Meta -> TC (Constrs Meta)

checkAlt lhs n sr (Alt Wildcard rhs) = bt ("ALT-WILDCARD") $ do
    checkCaseTree lhs rhs

checkAlt lhs n sr (Alt (Ctor ct args) rhs) = bt ("ALT-CTOR", pat) $ do
    argCtx <- checkDefs args

    -- check we've got a constructor
    cd <- lookup (ctName ct)
    when (defBody cd /= Abstract Postulate) $
        tcfail (NotConstructor $ ctName ct)

    -- Typechecking will be done eventually in the case for Leaf.
    cs <- with' (M.union argCtx) $
                checkCaseTree (subst n pat lhs) rhs
    return $ cs /\ scrutCs /\ ctCs (defR cd)
  where
    ctCs r = case ct of
        CT cn cr -> cr <--> r
        CTForced cn -> noConstrs

    ctor = case ct of
        CT cn cr -> V cn
        CTForced cn -> Forced (V cn)

    -- don't forget to rewrite in pat!
    pat = mkApp ctor [(r, V n) | Def n r ty (Abstract Var) cs <- args]

    -- bindings from the individual vars to the scrutinee
    scrutCs = unions [defR d --> sr | d <- args]

checkAlt lhs n sr (Alt (ForcedVal pat) rhs) = bt ("ALT-FORCED", pat) $ do
    checkCaseTree (subst n (Forced pat) lhs) rhs

checkTm :: Term -> TC (Type, Constrs Meta)

-- this is sketchy
checkTm (V Blank) = return (V Blank, noConstrs)

checkTm t@(V n) = bt ("VAR", n) $ do
    -- at the point of usage of a bound name,
    -- the constraints associated with that name come in
    d <- lookup n
    return (defType d, defConstraints d /\ Fixed R --> defR d)

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
    return (ty, defConstraints d /\ Fixed R --> defR d /\ convCs)

checkTm t@(Bind Lam [d@(Def n r ty (Abstract Var) _noCs)] tm) = bt ("LAM", t) $ do
    d' <- checkDef d
    (tmty, tmcs) <- with d' $ checkTm tm
    return (Bind Pi [d'] tmty, tmcs)

checkTm t@(Bind Pi [d@(Def n r ty (Abstract Var) _noCs)] tm) = bt ("PI", t) $ do
    d' <- checkDef d
    -- (tyty, _tycs) <- checkTm ty
    -- cs' <- conv (V $ UN "Type") tyty
    tmcs <- with d' $ do
        (tmty, tmcs) <- checkTm tm
        cs <- conv (V $ UN "Type") tmty
        return $ tmcs /\ cs
    return (V $ UN "Type", tmcs)

checkTm t@(Bind Let ds tm) = bt ("LET", t) $ do
    ds' <- checkDefs ds
    (tmty, tmcs) <- with' (M.union ds') $ checkTm tm
    return (tmty, tmcs)

checkTm t@(App app_r f x) = bt ("APP", t) $ do
    (fty, fcs) <- checkTm f
    (xty, xcs) <- checkTm x
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi [Def n' pi_r ty' (Abstract Var) _noCs] retTy -> do
            tycs <- conv xty ty'
            let cs =
                    -- we can't leave tycs out entirely because
                    -- if it's relevant, it needs to be erasure-correct as well
                    -- but if it's not used, then it needn't be erasure-correct
                    cond pi_r tycs
                    /\ fcs
                    /\ cond pi_r xcs
                    /\ pi_r <--> app_r
            return (subst n' x retTy, cs)

        _ -> do
            tcfail $ NonFunction f fty

checkTm (Forced tm) = bt ("FORCED", tm) $ do
    (ty, _cs) <- checkTm tm
    return (ty, noConstrs)

checkTm tm = bt ("UNCHECKABLE-TERM", tm) $ do
    tcfail $ UncheckableTerm tm

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

instantiate :: Monad m => m Int -> IM.IntMap Meta -> Def Meta -> m (Def Meta)
instantiate freshTag metaMap def = evalStateT refresh metaMap
  where
    refresh = defRelevance (freshen freshTag) def

-- left: from context (from outside), right: from expression (from inside)
conv :: Type -> Type -> TC (Constrs Meta)
conv p q = do
    ctx <- getCtx
    conv' (whnf ctx p) (whnf ctx q)

-- note that this function gets arguments in WHNF
conv' :: Type -> Type -> TC (Constrs Meta)

-- whnf is variable (something irreducible, constructor or axiom)
conv' (V n) (V n') = bt ("C-VAR", n, n') $ do
    require (n == n') $ Mismatch (show n) (show n')
    return noConstrs

conv' p@(Bind b [Def n r ty (Abstract Var) _noCs] tm) q@(Bind b' [Def n' r' ty' (Abstract Var) _noCs'] tm')
    = bt ("C-BIND", p, q) $ do
        require (b == b') $ Mismatch (show b) (show b')
        xs <- conv ty ty' -- (rename n' n ty')
        ys <- with (Def n r ty (Abstract Var) noConstrs)
                $ conv tm (rename n' n tm')
        return $ xs /\ ys /\ r <--> r'

{- This would be necessary for conversion-checking of multilets. Let's disable them for now.
conv' (Bind b (d:ds) tm) (Bind b' (d':ds') tm') = bt ("C-SIMPL", b) $
    conv' (Bind b [d] $ Bind b ds tm) (Bind b' [d'] $ Bind b' ds' tm')
-}

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    xs <- conv f f'
    ys <- conv x x'
    return $ xs /\ ys /\ r <--> r'

-- we don't include a case for Forced because those constructors
-- get normalised away to bare terms

conv' p q = tcfail $ CantConvert p q
