module Erasure.Check (check) where

import TT
import TTLens
import Whnf
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

import Debug.Trace

data TCError
    = CantConvert TTmeta TTmeta
    | CantConvertAlt (Alt Meta) (Alt Meta)
    | Mismatch String String
    | UnknownName Name
    | WrongType TTmeta TTmeta  -- term, type
    | BadCtorType TTmeta
    | NonFunction TTmeta TTmeta  -- term, type
    | EmptyCaseTree TTmeta
    | CantMatch TTmeta TTmeta
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

cond :: Meta -> Constrs -> Constrs
cond r = CS . M.mapKeysWith S.union (S.insert r) . runCS

with :: Def Meta Constrs' -> TC a -> TC a
with d@(Def n r ty mtm mcs) = local $ \(tb, ctx) -> (tb, M.insert n d ctx)

bt :: Show a => a -> TC b -> TC b
bt dbg = local . first $ (show dbg :)

tcfail :: TCError -> TC a
tcfail e = do
    (tb, ctx) <- ask
    lift . throwE $ TCFailure e tb

getCtx :: TC (Ctx Meta Constrs')
getCtx = snd <$> ask

require :: Bool -> TCError -> TC ()
require True  e = return ()
require False e = tcfail e

lookup :: Name -> TC (Def Meta Constrs')
lookup n = do
    (tb, ctx) <- ask
    case M.lookup n ctx of
        Just x  -> return x
        Nothing -> tcfail $ UnknownName n

freshTag :: TC Int
freshTag = lift $ lift (modify (+1) >> get)

runTC :: Int -> Ctx Meta Constrs' -> TC a -> Either TCFailure a
runTC maxTag ctx tc = evalState (runExceptT $ runReaderT tc ([], ctx)) maxTag

check :: Program Meta VoidConstrs -> Either TCFailure (Ctx Meta Constrs', Constrs)
check prog@(Prog defs) = runTC maxTag M.empty $ checkDefs (CS M.empty) defs
  where
    getTag (MVar i) = i
    getTag _        = 0  -- whatever, we're looking for maximum

    allTags = prog ^.. progRelevance . to getTag
    maxTag = L.maximum allTags

checkDefs :: Constrs -> [Def Meta VoidConstrs] -> TC (Ctx Meta Constrs', Constrs)
checkDefs cs [] = do
    ctx <- getCtx
    return (ctx, cs)
checkDefs cs (d:ds) = do
    Def n r ty mtm dcs <- with (bare d) $ checkDef d
    let dcs' = reduce <$> dcs
    with (Def n r ty mtm dcs')
        $ checkDefs (fromMaybe noConstrs dcs' `union` cs) ds
  where
    bare (Def n r ty mtm Nothing) = Def n r ty mtm Nothing

checkDef :: Def Meta VoidConstrs -> TC (Def Meta Constrs')
checkDef (Def n r ty Nothing Nothing) = return $ Def n r ty Nothing Nothing
checkDef (Def n r ty (Just tm) Nothing) = bt ("DEF", n) $ do
    (tmty, tmcs) <- checkTm tm
    tycs <- conv ty tmty
    let cs = tycs /\ tmcs
    return $ Def n r ty (Just tm) (Just cs)

checkTm :: Term -> TC (Type, Constrs)

checkTm t@(V n) = bt ("VAR", n) $ do
    Def _n r ty mtm mcs <- lookup n
    return (ty, Fixed R --> r)

checkTm t@(I n ty) = bt ("INST", n, ty) $ do
    Def _n r nty mtm mcs <- lookup n
    i <- freshTag
    let (ty', cs') = undefined -- instantiate i (nty, fromMaybe noConstrs mcs)
    convCs <- conv ty' ty
    return (ty', cs' /\ convCs /\ Fixed R --> r)

checkTm t@(Bind Lam n r ty tm) = bt ("LAM", t) $ do
    (tmty, tmcs) <- with (Def n r ty Nothing Nothing) $ checkTm tm
    return (Bind Pi n r ty tmty, tmcs)

checkTm t@(Bind Pi n r ty tm) = bt ("PI", t) $ do
    (tmty, tmcs) <- with (Def n r ty Nothing Nothing) $ checkTm tm
    return (Type, tmcs)

checkTm t@(Bind Pat n r ty tm) = bt ("PAT", t) $ do
    (tmty, tmcs) <- with (Def n r ty Nothing Nothing) $ checkTm tm
    return (Bind Pat n r ty tmty, tmcs)

checkTm t@(App app_r f x) = bt ("APP", t) $ do
    (fty, fcs) <- checkTm f
    (xty, xcs) <- checkTm x
    case fty of
        Bind Pi n' pi_r ty' retTy -> do
            tycs <- conv xty ty'
            let cs =
                    tycs
                    /\ fcs
                    /\ cond pi_r xcs
                    /\ pi_r <--> app_r
            return (subst n' x retTy, cs)

        _ -> do
            tcfail $ NonFunction f fty

checkTm t@(Let (Def n r ty mtm Nothing) tm) = bt ("LET", t) $ do
    letcs <- case mtm of
        Just t -> do
            (valty, valcs) <- checkTm $ fromMaybe Erased mtm
            tycs <- conv ty valty
            return $ Just (valcs /\ tycs)
        Nothing -> return Nothing

    (tmty, tmcs) <-
        with (Def n r ty mtm letcs)
            $ checkTm tm
    return (tmty, tmcs /\ fromMaybe noConstrs letcs)

checkTm t@(Case s alts) = bt ("CASE", t) $ do
    (sty, scs) <- checkTm s
    alts' <- mapM checkAlt alts
    let cs = scs /\ unions [cs | (alt, cs) <- alts']
    let ty = Case s [alt | (alt, cs) <- alts']
    return (ty, cs)

checkTm Erased = return (Erased, noConstrs)
checkTm Type   = return (Type,   noConstrs)

checkAlt :: Alt Meta -> TC (Alt Meta, Constrs)
checkAlt (DefaultCase tm) = bt ("ALT-DEF", tm) $ do
    (tmty, tmcs) <- checkTm tm
    return (DefaultCase tmty, tmcs)

checkAlt (ConCase cn tm) = bt ("ALT-CON", cn, tm) $ do
    Def _cn cr cty Nothing Nothing <- lookup cn
    (tmty, tmcs) <- checkTm tm
    argcs <- matchArgs cty args
    return (ConCase cn tmty, tmcs /\ argcs)
  where
    (args, rhs) = splitBinder Pat tm
    matchArgs p@(Bind Pi n r ty tm) q@((n', r', ty') : as) = bt ("MATCH-ARGS", p, q) $ do
        xs <- conv ty ty'
        ys <- matchArgs tm as
        return $ xs /\ ys /\ r' --> r  -- ?direction?
    matchArgs p q = return noConstrs

{-
instantiate :: Int -> (Type, Constrs) -> (Type, Constrs)
instantiate tag (ty, CS cs) = (ty', CS cs')
  where
    ty' = ty & ttRelevance %~ tagMeta tag
    cs' = M.mapKeysWith S.union tagSet . M.map tagSet $ cs
    tagSet = S.map $ tagMeta tag
    newMetas = views ttRelevance S.singleton ty
-}

-- left: from context (from outside), right: from expression (from inside)
conv :: Type -> Type -> TC Constrs
conv p q = do
    ctx <- getCtx
    conv' (whnf ctx p) (whnf ctx q)

-- note that this function gets arguments in WHNF
conv' :: Type -> Type -> TC Constrs

-- whnf is variable (something irreducible, constructor or axiom)
conv' (V n) (V n') = bt ("C-VAR", n, n') $ do
    require (n == n') $ Mismatch n n'
    return noConstrs

conv' p@(Bind b n r ty tm) q@(Bind b' n' r' ty' tm') = bt ("C-BIND", p, q) $ do
    require (b == b') $ Mismatch (show b) (show b')
    xs <- conv ty (rename [n'] [n] ty')
    ys <- with (Def n r ty Nothing Nothing) $ conv tm (rename [n'] [n] tm')
    return $ xs /\ ys /\ r <--> r'

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    xs <- conv f f'
    ys <- conv x x'
    return $ xs /\ ys /\ r <--> r'

conv' p@(Let (Def n r ty mtm Nothing) tm) q@(Let (Def n' r' ty' mtm' Nothing) tm') = bt ("C-LET", p, q) $ do
    (val, val') <- case (mtm, mtm') of
        (Just t, Just t') -> return (t, t')
        (Nothing, Nothing) -> return (Erased, Erased)
        _ -> tcfail $ Mismatch (show mtm) (show mtm')

    xs <- conv ty (rename [n'] [n] ty')
    (valty, valcs) <- checkTm val
    tycs <- conv ty valty
    vcs <- conv val val'
    let letcs = valcs /\ tycs
    ys <- with (Def n r ty mtm (Just letcs)) $ conv tm (rename [n'] [n] tm')
    return $ letcs /\ ys /\ vcs /\ r <--> r'

conv' p@(Case s alts) q@(Case s' alts') = bt ("C-CASE", p, q) $ do
    require (length alts == length alts') $ Mismatch (show alts) (show alts')
    xs <- conv s s'
    (sty, scs) <- checkTm s
    acs <- unions <$> zipWithM (convAlt sty) (L.sort alts) (L.sort alts')
    return $ xs /\ scs /\ acs

-- last resort: uniform-case test
conv' p@(Case _ _) q = conv' q p  -- won't loop because q /= Case
conv' p q@(Case s alts) = bt ("UNIF-CASE", p, q) $ uniformCase p alts

conv' Type   Type   = return noConstrs
conv' Erased Erased = return noConstrs

conv' p q = tcfail $ CantConvert p q

convAlt :: Type -> Alt Meta -> Alt Meta -> TC Constrs
convAlt sty (DefaultCase tm) (DefaultCase tm') = bt ("CA-DEF", tm, tm') $ conv tm tm'
convAlt sty p@(ConCase cn tm) q@(ConCase cn' tm') = bt ("CA-CON", p, q) $ do
    require (cn == cn') $ Mismatch cn cn'
    Def _cn cr cty Nothing Nothing <- lookup cn
    let (ctyArgs, ctyRet) = splitBinder Pi cty
    (xs, ctx) <- match ctyRet sty
    ys <- conv (substMatch ctx cty tm) (substMatch ctx cty tm')
    return $ xs /\ ys

uniformCase :: Term -> [Alt Meta] -> TC Constrs
uniformCase target alts = unions <$> mapM (simpleAlt target) alts
  where
    simpleAlt target (DefaultCase tm) = conv target tm
    simpleAlt target (ConCase cn tm) = conv target $ snd (splitBinder Pat tm)
    
-- pattern, term
match :: TT Meta -> TT Meta -> TC (Constrs, M.Map Name Term)
match (V n) (V n') | n == n' = return (noConstrs, M.empty)
match (V n) tm = return (noConstrs, M.singleton n tm)
match (App r f x) (App r' f' x') = do
    (xs, xmap) <- match f f'
    (ys, ymap) <- match x x'
    return (xs /\ ys /\ r <--> r', M.union xmap ymap)

-- ctx, ctor type, pat+rhs
substMatch :: M.Map Name Term -> Term -> Term -> Term
substMatch ctx (Bind Pi n r ty tm) (Bind Pat n' r' ty' tm')
    | Just x <- M.lookup n ctx
    = substMatch ctx (subst n x tm) (subst n' x tm')

    | otherwise
    = substMatch ctx tm tm'
substMatch ctx ctyRet rhs = rhs

rename :: [Name] -> [Name] -> TTmeta -> TTmeta
rename [] [] tm = tm
rename (n : ns) (n' : ns') tm = rename ns ns' $ subst n (V n') tm
rename _ _ _ = error "rename: incoherent args"
