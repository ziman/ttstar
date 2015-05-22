module Erasure.Check (check) where

import TT
import Whnf
import Erasure.Meta
import qualified Erasure.Solve as Solve
import Erasure.Solve hiding (reduce)

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

runTC :: Ctx Meta Constrs -> TC a -> Either TCFailure a
runTC ctx tc = evalState (runExceptT $ runReaderT tc ([], ctx)) 0

check :: Program Meta -> Either TCFailure Constrs
check (Prog defs) = runTC M.empty $ checkDefs M.empty defs

checkDefs :: Constrs -> [Def Meta] -> TC Constrs
checkDefs cs [] = return cs
checkDefs cs (d:ds) = do
    (n, r, ty, mtm, dcs) <- checkDef d
    with' n r ty mtm dcs
        $ checkDefs (dcs `union` cs) ds

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
    return (r, ty, cs)

checkTm t@(Bind Lam n r ty tm) = bt ("LAM", t) $ do
    (tmr, tmty, tmcs) <- with n r ty $ checkTm tm
    return (tmr, Bind Pi n r ty tmty, tmcs)

checkTm t@(Bind Pi n r ty tm) = bt ("PI", t) $ do
    (tmr, tmty, tmcs) <- with n r ty $ checkTm tm
    return (tmr, Type, tmcs)

checkTm t@(Bind Pat n r ty tm) = bt ("PAT", t) $ do
    (tmr, tmty, tmcs) <- with n r ty $ checkTm tm
    return (tmr, Bind Pat n r ty tmty, tmcs)

checkTm t@(App r f x) = bt ("APP", t) $ do
    (fr, fty, fcs) <- checkTm f
    (xr, xty, xcs) <- checkTm x
    case fty of
        Bind Pi n' r' ty' retTy -> do
            tycs <- conv xty ty'
            let cs = tycs /\ fcs /\ cond r xcs /\ r --> r'
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
checkAlt (DefaultCase tm) = do
    (tmr, tmty, tmcs) <- checkTm tm
    return (tmr, DefaultCase tmty, tmcs)

checkAlt (ConCase cn r tm) = do
    (cr, cty, Nothing, ccs) <- lookup cn
    (tmr, tmty, tmcs) <- checkTm tm
    argcs <- matchArgs cty args
    return (tmr, ConCase cn r tmty, tmcs /\ argcs)
  where
    (args, rhs) = splitBinder Pat tm
    matchArgs (Bind Pi n r ty tm) ((n', r', ty') : as) = do
        xs <- conv ty ty'
        ys <- matchArgs tm as
        return $ xs /\ ys /\ r' --> r

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

{-
freshen :: TC TTmeta -> TC TTmeta
freshen tc = tc

cond :: Meta -> TC a -> TC a
cond m = mapReaderT $ censor (S.map mogrify)
  where
    mogrify (us :<-: gs) = us :<-: S.insert m gs

bt :: Show a => a -> TC b -> TC b
bt dbg = local . first $ (show dbg :)

require :: Bool -> TCError -> TC ()
require True  _ = return ()
require False e = tcfail e

eq :: Meta -> Meta -> Constrs
eq r r' = S.unions [[r] <~ [r'], [r'] <~ [r]]

conv :: TTmeta -> TTmeta -> TC ()
conv (V n) (V n') = bt ("C-VAR", n, n') $ do
    require (n == n') $ Mismatch n n'

conv p@(Bind b r n ty tm) q@(Bind b' r' n' ty' tm') = bt ("C-BIND", p, q) $ do
    require (b == b') $ Mismatch (show b) (show b')
    emit (r `eq` r')
    conv ty (rename [n'] [n] ty')  -- check convertibility of the type
    add r n ty' $ conv tm (rename [n'] [n] tm')  -- knowing the type, check the rest

conv p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    conv f f'
    conv x x'
    emit (r `eq` r')

conv p@(Case s alts) q@(Case s' alts') = bt ("C-CASE", p, q) $ do
    require (length alts == length alts') $ Mismatch (show alts) (show alts')
    conv s s'
    sty <- checkTm s
    zipWithM_ (convAlt sty) (L.sort alts) (L.sort alts')

-- last-resort: uniform-case check
conv x@(Case _ _) y = conv y x
conv x (Case s alts) = bt ("C-UNIFORM-CASE", x, alts) $ uniformCase x alts

conv Type Type = return ()
conv Erased Erased = return ()

conv tm tm' = tcfail $ CantConvert tm tm'

convAlt :: TT Meta -> Alt Meta -> Alt Meta -> TC ()
convAlt sty (DefaultCase tm) (DefaultCase tm') = conv tm tm'
convAlt sty p@(ConCase cn r tm) q@(ConCase cn' r' tm') = bt ("CONV-ALT", p, q) $ do
    require (cn == cn') $ Mismatch cn cn'
    emit (r `eq` r')
    (cr, cty, Nothing) <- lookupName cn
    let (ctyArgs, ctyRet) = splitBinder Pi cty
    ctx <- match ctyRet sty
    conv (substMatch ctx cty tm) (substMatch ctx cty tm')
convAlt sty x y = tcfail $ CantConvertAlt x y

-- ctx, ctor type, pat+rhs
substMatch :: M.Map Name (TT Meta) -> TT Meta -> TT Meta -> TT Meta
substMatch ctx (Bind Pi r n ty tm) (Bind Pat r' n' ty' tm')
    | Just x <- M.lookup n ctx
    = substMatch ctx (subst n x tm) (subst n' x tm')

    | otherwise
    = substMatch ctx tm tm'
substMatch ctx ctyRet rhs = rhs

-- pattern, term
match :: TT Meta -> TT Meta -> TC (M.Map Name (TT Meta))
match (V n) (V n') | n == n' = return $ M.empty
match (V n) tm = return $ M.singleton n tm
match (App r f x) (App r' f' x') = do
    emit (r `eq` r')
    xs <- match f f'
    ys <- match x x'
    return $ M.union xs ys

unPi :: TT Meta -> [(Name, Meta, TT Meta)] -> ([(Name, Meta, TT Meta)], TT Meta)
unPi (Bind Pi r n ty tm) args = unPi tm ((n, r, ty) : args)
unPi tm args = (args, tm)

uniformCase :: TTmeta -> [Alt Meta] -> TC ()
uniformCase  _ []     = return ()
uniformCase  x (a:as) = conv x (snd . splitBinder Pat $ getTm a) >> uniformCase x as
  where
    getTm (DefaultCase tm) = tm
    getTm (ConCase _cn _r tm) = tm

add :: Meta -> Name -> TTmeta -> TC a -> TC a
add r n ty = local . second $ M.insert n (r, ty, Nothing)

infix 3 <~
(<~) :: [Meta] -> [Meta] -> Constrs
us <~ gs = S.singleton (S.fromList us :<-: S.fromList gs)

steps :: [TC Constrs] -> TC Constrs
steps = fmap S.unions . sequence

freshInt :: TC Int
freshInt = lift . lift . lift $ modify (+1) *> get

tcfail :: TCError -> TC a
tcfail e = do
    (tb, ctx) <- ask
    lift . lift . throwE $ TCFailure e tb

emit :: Constrs -> TC ()
emit = lift . tell

lookupName :: Name -> TC (Meta, TTmeta, Maybe TTmeta)
lookupName n = do
    (tb, ctx) <- ask
    case M.lookup n ctx of
        Just x -> return x
        Nothing -> tcfail $ UnknownName n

halfRunTC :: TCCtx -> TC a -> HalfTC (a, Constrs)
halfRunTC ctx tc = runWriterT $ runReaderT tc ([], ctx)

halfExecTC :: TCCtx -> TC a -> HalfTC Constrs
halfExecTC ctx tc = execWriterT $ runReaderT tc ([], ctx)

runHalfTC :: TCState -> HalfTC a -> Either TCFailure a
runHalfTC st htc = evalState (runExceptT htc) st

check :: Program Meta -> Either TCFailure Constrs
check prog = runHalfTC 0 $ checkProgram prog

reduce' :: TT Meta -> TC (TT Meta)
reduce' tm = do
    (tb, ctx) <- ask
    return $ reduce ctx tm

checkProgram :: Program Meta -> HalfTC Constrs
checkProgram (Prog defs) = halfExecTC M.empty $ mapM_ checkDef defs

checkDefs :: TCCtx -> Constrs -> [Def Meta] -> HalfTC Constrs
checkDefs ctx cs [] = return cs
checkDefs ctx cs (d:ds) = do
    (dctx, dcs) <- halfRunTC ctx $ checkDef d
    let (uses, rdcs) = Solve.reduce dcs
    if Fixed I `S.member` uses
        then throwE $ TCFailure (InconsistentErasure $ defName d) []
        else checkDefs (M.union dctx ctx) (S.union rdcs cs) ds
  where
    defName (Def r n ty _) = n

checkDef :: Def Meta -> TC TCCtx
checkDef (Def r n ty Axiom) = return $ M.singleton n (r, ty, Nothing)
checkDef (Def r n ty (Fun tm)) = bt ("FUNDECL", n) $ do
    tmTy <- reduce' =<< checkTm tm
    ty' <- reduce' ty
    bt ("RET-TY", ty', tmTy) $ conv ty' tmTy
    return $ M.singleton n (r, ty, Just tm)

checkTm :: TTmeta -> TC TTmeta
checkTm t@(V n) = bt ("VAR", t) $ do
    (r, ty, _def) <- lookupName n
    emit ([r] <~ [Fixed R])
    -- TODO: freshen
    return ty

checkTm t@(Bind Pi r n ty tm) = bt ("PI", t) $ do
    conv Type =<< add r n ty (checkTm tm)
    return $ Type

checkTm t@(Bind Lam r n ty tm) = bt ("LAM", t) $
    Bind Pi r n ty <$> add r n ty (checkTm tm)

checkTm t@(Bind Pat r n ty tm) = bt ("PAT", t) $
    Bind Pat r n ty <$> add r n ty (checkTm tm)

checkTm t@(App r f x) = bt ("APP", t) $ do
    fTy <- bt ("APP-F", f) $ checkTm f
    xTy <- bt ("APP-X", x) $ cond r $ checkTm x
    case fTy of
        Bind Pi r' n' ty' tm' -> do
            emit (r `eq` r')
            conv ty' xTy
            reduce' $ subst n' x tm'

        _ -> tcfail $ NonFunction f fTy

checkTm t@(Case s alts) = bt ("CASE", t) $ do
    _sTy <- checkTm s  -- we ignore scrutinee type
    alts' <- mapM checkAlt alts
    return $ Case s alts'

checkTm Erased = return $ Erased
checkTm Type   = return $ Type  -- type-in-type

checkAlt :: Alt Meta -> TC (Alt Meta)
checkAlt (DefaultCase tm) = DefaultCase <$> checkTm tm
checkAlt (ConCase cn r tm) = bt ("CONCASE", cn, tm) $ do
    (cr, cty, _def) <- lookupName cn
    matchArgs cty args
    emit (cr `eq` r)
    ConCase cn r <$> checkTm tm
  where
    (args, rhs) = splitBinder Pat tm
    matchArgs (Bind Pi r n ty tm) ((n', r', ty'):as) = do
        emit (r `eq` r')
        conv ty ty'
        matchArgs tm as
    matchArgs _ _ = return ()
-}
