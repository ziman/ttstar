module Erasure.Check (check) where

import TT
import Whnf
import Erasure.Meta
import Erasure.Solve

import Prelude hiding (lookup)

import Control.Monad
import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

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

type TCState = Int
type TCTraceback = [String]
type TC a = ReaderT (TCTraceback, Ctx Meta Constrs) (ExceptT TCFailure (State TCState)) a
type Sig = (Meta, Type, Constrs)  -- relevance, type, constraints

type Term = TT Meta
type Type = TT Meta

infixl 2 /\
(/\) :: Constrs -> Constrs -> Constrs
(/\) = union

infix 3 -->
(-->) :: Meta -> Meta -> Constrs
g --> u = M.singleton (S.singleton g) (S.singleton u)

infix 3 <-->
(<-->) :: Meta -> Meta -> Constrs
p <--> q = p --> q /\ q --> p

eq :: Meta -> Meta -> Constrs
eq p q = p <--> q

union :: Constrs -> Constrs -> Constrs
union = M.unionWith S.union

unions :: [Constrs] -> Constrs
unions = M.unionsWith S.union

noConstrs :: Constrs
noConstrs = M.empty

cond :: Meta -> Constrs -> Constrs
cond r = M.mapKeysWith S.union $ S.insert r

with' :: Name -> Meta -> Type -> Maybe Term -> Constrs -> TC a -> TC a
with' n r ty mtm cs = local $ \(tb, ctx) -> (tb, M.insert n (r, ty, mtm, cs) ctx)

with :: Name -> Meta -> Type -> TC a -> TC a
with n r ty = with' n r ty Nothing noConstrs

bt :: Show a => a -> TC b -> TC b
bt dbg = local . first $ (show dbg :)

tcfail :: TCError -> TC a
tcfail e = do
    (tb, ctx) <- ask
    lift . throwE $ TCFailure e tb

getCtx :: TC (Ctx Meta Constrs)
getCtx = snd <$> ask

require :: Bool -> TCError -> TC ()
require True  e = return ()
require False e = tcfail e

lookup :: Name -> TC (Meta, Type, Maybe Term, Constrs)
lookup n = do
    (tb, ctx) <- ask
    case M.lookup n ctx of
        Just x  -> return x
        Nothing -> tcfail $ UnknownName n

freshTag :: TC Int
freshTag = lift $ lift (modify (+1) >> get)

runTC :: Ctx Meta Constrs -> TC a -> Either TCFailure a
runTC ctx tc = evalState (runExceptT $ runReaderT tc ([], ctx)) 0

check :: Program Meta -> Either TCFailure (Ctx Meta Constrs, Constrs)
check (Prog defs) = runTC M.empty $ checkDefs M.empty defs

checkDefs :: Constrs -> [Def Meta] -> TC (Ctx Meta Constrs, Constrs)
checkDefs cs [] = do
    ctx <- getCtx
    return (ctx, cs)
checkDefs cs (d:ds) = do
    (n, r, ty, mtm, dcs) <- checkDef d
    let dcs' = reduce dcs
    with' n r ty mtm dcs'
        $ checkDefs (dcs' `union` cs) ds

checkDef :: Def Meta -> TC (Name, Meta, Type, Maybe Term, Constrs)
checkDef (Def n r ty Axiom) = return (n, r, ty, Nothing, noConstrs)
checkDef (Def n r ty (Fun tm)) = bt ("DEF", n) $ do
    (tmr, tmty, tmcs) <- checkTm tm
    tycs <- conv ty tmty
    let cs = tycs /\ tmcs /\ r --> tmr
    return (n, r, ty, Just tm, cs)

checkTm :: Term -> TC (Meta, Type, Constrs)

checkTm t@(V n) = bt ("VAR", n) $ do
    (r, ty, mtm, cs) <- lookup n
    tag <- freshTag
    return (r, tagTm tag ty, tagConstrs tag cs)

checkTm t@(Bind Lam n r ty tm) = bt ("LAM", t) $ do
    (tmr, tmty, tmcs) <- with n r ty $ checkTm tm
    return (tmr, Bind Pi n r ty tmty, tmcs)

checkTm t@(Bind Pi n r ty tm) = bt ("PI", t) $ do
    (tmr, tmty, tmcs) <- with n r ty $ checkTm tm
    return (tmr, Type, tmcs)

checkTm t@(Bind Pat n r ty tm) = bt ("PAT", t) $ do
    (tmr, tmty, tmcs) <- with n r ty $ checkTm tm
    return (tmr, Bind Pat n r ty tmty, tmcs)

checkTm t@(App app_r f x) = bt ("APP", t) $ do
    (fr, fty, fcs) <- checkTm f
    (xr, xty, xcs) <- checkTm x
    case fty of
        Bind Pi n' pi_r ty' retTy -> do
            tycs <- conv xty ty'
            let cs = tycs /\ fcs /\ cond pi_r xcs /\ pi_r --> app_r /\ app_r --> xr
            return (fr, subst n' x retTy, cs)

        _ -> do
            tcfail $ NonFunction f fty

checkTm t@(Case s alts) = bt ("CASE", t) $ do
    (sr, sty, scs) <- checkTm s
    alts' <- mapM checkAlt alts
    let cs = scs /\ unions [cs /\ sr --> r | (r, ty, cs) <- alts']
    let ty = Case s [ty | (r, ty, cs) <- alts']
    return (sr, ty, cs)

checkTm Erased = return (Fixed I, Erased, noConstrs)
checkTm Type   = return (Fixed I, Type,   noConstrs)

checkAlt :: Alt Meta -> TC (Meta, Alt Meta, Constrs)
checkAlt (DefaultCase tm) = bt ("ALT-DEF", tm) $ do
    (tmr, tmty, tmcs) <- checkTm tm
    return (tmr, DefaultCase tmty, tmcs)

checkAlt (ConCase cn r tm) = bt ("ALT-CON", cn, tm) $ do
    (cr, cty, Nothing, ccs) <- lookup cn
    (tmr, tmty, tmcs) <- checkTm tm
    argcs <- matchArgs cty args
    return (tmr, ConCase cn r tmty, tmcs /\ argcs)
  where
    (args, rhs) = splitBinder Pat tm
    matchArgs p@(Bind Pi n r ty tm) q@((n', r', ty') : as) = bt ("MATCH-ARGS", p, q) $ do
        xs <- conv ty ty'
        ys <- matchArgs tm as
        return $ xs /\ ys /\ r' --> r
    matchArgs p q = return noConstrs

tagMeta :: Int -> Meta -> Meta
tagMeta tag (MVar i j)
    | tag <= j = error "tagMeta: tag not fresh"
    | otherwise = MVar i tag
tagMeta tag m = m

tagTm :: Int -> Term -> Term
tagTm tag = fmap $ tagMeta tag

tagConstrs :: Int -> Constrs -> Constrs
tagConstrs tag = M.mapKeysWith S.union tagSet . M.map tagSet
  where
    tagSet = S.map $ tagMeta tag

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
    ys <- with n r ty $ conv tm (rename [n'] [n] tm')
    return $ xs /\ ys /\ r <--> r'

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    xs <- conv f f'
    ys <- conv x x'
    return $ xs /\ ys /\ r <--> r'

conv' p@(Case s alts) q@(Case s' alts') = bt ("C-CASE", p, q) $ do
    require (length alts == length alts') $ Mismatch (show alts) (show alts')
    xs <- conv s s'
    (sr, sty, scs) <- checkTm s
    acs <- unions <$> zipWithM (convAlt sr sty) (L.sort alts) (L.sort alts')
    return $ xs /\ scs /\ acs

-- last resort: uniform-case test
conv' p@(Case _ _) q = conv' q p  -- won't loop because q /= Case
conv' p q@(Case s alts) = bt ("UNIF-CASE", p, q) $ uniformCase p alts

conv' Type   Type   = return noConstrs
conv' Erased Erased = return noConstrs

conv' p q = tcfail $ CantConvert p q

convAlt :: Meta -> Type -> Alt Meta -> Alt Meta -> TC Constrs
convAlt sr sty (DefaultCase tm) (DefaultCase tm') = bt ("CA-DEF", tm, tm') $ conv tm tm'
convAlt sr sty p@(ConCase cn r tm) q@(ConCase cn' r' tm') = bt ("CA-CON", p, q) $ do
    require (cn == cn') $ Mismatch cn cn'
    (cr, cty, Nothing, _empty) <- lookup cn
    let (ctyArgs, ctyRet) = splitBinder Pi cty
    (xs, ctx) <- match ctyRet sty
    ys <- conv (substMatch ctx cty tm) (substMatch ctx cty tm')
    return $ xs /\ ys /\ r <--> r'

uniformCase :: Term -> [Alt Meta] -> TC Constrs
uniformCase target alts = unions <$> mapM (simpleAlt target) alts
  where
    simpleAlt target (DefaultCase tm) = conv target tm
    simpleAlt target (ConCase cn r tm) = conv target $ snd (splitBinder Pat tm)
    
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
