module Erasure.Check where

import TTstar
import Erasure.Meta

import Control.Monad
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer

import qualified Data.Map as M
import qualified Data.Set as S

type Guards = S.Set Meta
type Uses = S.Set Meta
data Constr = Uses :<-: Guards deriving (Eq, Ord)
type Constrs = S.Set Constr
type Ctx = M.Map Name (Meta, TTmeta)

instance Show Constr where
    show (us :<-: gs) = show (S.toList us) ++ " <- " ++ show (S.toList gs)

data TCError
    = CantConvert TTmeta TTmeta
    | Mismatch String String
    | UnknownName Name
    | WrongType TTmeta TTmeta  -- term, type
    | BadCtorType TTmeta
    | NonFunction TTmeta TTmeta  -- term, type
    | EmptyCaseTree TTmeta
    | Other String
    deriving (Eq, Ord, Show)

type TCState = Int
type TC a = WriterT Constrs (ExceptT TCError (State TCState)) a

cond :: Meta -> Constrs -> Constrs
cond m = S.map mogrify
  where
    mogrify (us :<-: gs) = us :<-: S.insert m gs

require :: Bool -> TCError -> TC ()
require True  e = return ()
require False e = tcfail e

eq :: Meta -> Meta -> Constrs
eq r r' = S.unions [[r] <~ [r'], [r'] <~ [r]]

rename :: [Name] -> [Name] -> TTmeta -> TTmeta
rename [] [] tm = tm
rename (n : ns) (n' : ns') tm = rename ns ns' $ subst n (V n') tm

conv :: TTmeta -> TTmeta -> TC ()
conv (V n) (V n') =
    require (n == n') $ Mismatch n n'

conv (Bind b r n ty tm) (Bind b' r' n' ty' tm') = do
    require (b == b') $ Mismatch (show b) (show b')
    conv ty $ rename [n'] [n] ty'
    conv tm $ rename [n'] [n] tm'
    tell (r `eq` r')

conv (App r f x) (App r' f' x') = do
    conv f f'
    conv x x'
    tell (r `eq` r')

conv (Prim op) (Prim op') =
    require (op == op') $ Mismatch (show op) (show op')

conv (Case s alts) (Case s' alts') = do
    conv s s'
    require (length alts == length alts') $ Mismatch (show alts) (show alts')
    zipWithM_ convAlt alts alts'

conv (C c) (C c') =
    require (c == c') $ Mismatch (show c) (show c')

conv tm tm' = tcfail $ CantConvert tm tm'

convAlt :: Alt Meta -> Alt Meta -> TC ()
convAlt (DefaultCase tm) (DefaultCase tm') = conv tm tm'
convAlt (ConstCase c tm) (ConstCase c' tm') = do
    require (c == c') $ Mismatch (show c) (show c')
    conv tm tm'
convAlt (ConCase cn r ns tm) (ConCase cn' r' ns' tm') = do
    require (cn == cn') $ Mismatch cn cn'
    require (length ns == length ns') $ Mismatch (show ns) (show ns')
    conv tm $ rename ns' ns tm'
    tell (r `eq` r')

add :: Meta -> Name -> TTmeta -> Ctx -> Ctx
add r n ty = M.insert n (r, ty)

infix 3 <~
(<~) :: [Meta] -> [Meta] -> Constrs
us <~ gs = S.singleton (S.fromList us :<-: S.fromList gs)

steps :: [TC Constrs] -> TC Constrs
steps = fmap S.unions . sequence

freshN :: TC Name
freshN = lift . lift $ do
    i <- get
    put $ i+1
    return $ "_" ++ show i

tcfail :: TCError -> TC a
tcfail = lift . throwE

lookupName :: Ctx -> Name -> TC (Meta, TTmeta)
lookupName ctx n
    | Just x <- M.lookup n ctx = return x
    | otherwise = tcfail $ UnknownName n

check :: Program Meta -> Either TCError Constrs
check prog = evalState (runExceptT . execWriterT $ checkProgram prog) 0

checkProgram :: Program Meta -> TC ()
checkProgram (Prog defs) = mapM_ (checkDef globals) defs
  where
    globals :: Ctx
    globals = M.fromList [(n, (r, ty)) | Def r n ty dt <- defs]

checkDef :: Ctx -> Def Meta -> TC ()
checkDef ctx (Def r n ty Ctor) = return ()
checkDef ctx (Def r n ty (Fun tm)) = conv ty =<< checkTm ctx tm

checkTm :: Ctx -> TTmeta -> TC TTmeta
checkTm ctx (V n) = do
    (r, ty) <- lookupName ctx n
    tell ([r] <~ [Fixed R])
    return ty

checkTm ctx (Bind Pi r n ty tm) = do
    conv (C TType) =<< checkTm (add r n ty ctx) tm
    return $ C TType

checkTm ctx (Bind Lam r n ty tm) =
    Bind Pi r n ty <$> checkTm (add r n ty ctx) tm

checkTm ctx (App r f x) = do
    fTy <- checkTm ctx f
    xTy <- checkTm ctx x
    case fTy of
        Bind Pi r' n' ty' tm' -> do
            tell (r `eq` r')
            return $ subst n' x tm'

        _ -> tcfail $ NonFunction f fTy

checkTm ctx (Prim op) = return $ primType Fixed op

checkTm ctx t@(Case s alts) = do
    sTy <- checkTm ctx s
    altsTy <- mapM (checkAlt ctx) alts  -- we ignore scrutinee type, it's been checked anyway
    case altsTy of
        [] -> tcfail $ EmptyCaseTree t
        aty:atys -> do
            mapM_ (conv aty) atys
            return aty

checkTm ctx (C c) = return $ constType c

checkAlt :: Ctx -> Alt Meta -> TC TTmeta
checkAlt ctx (DefaultCase tm) = checkTm ctx tm
checkAlt ctx (ConstCase c tm) = checkTm ctx tm
checkAlt ctx (ConCase cn r ns tm) = do
    (cr, cty) <- lookupName ctx cn
    ctx' <- augCtx ctx ns cty
    checkTm ctx' tm
  where
    augCtx :: Ctx -> [Name] -> TTmeta -> TC Ctx
    augCtx ctx [] ty = return ctx
    augCtx ctx (n : ns) (Bind Pi r n' ty tm) = augCtx (add r n ty ctx) ns tm
    augCtx ctx (n : ns) tm = tcfail $ BadCtorType tm

{-
checkTerm :: Ctx -> TTmeta -> TTmeta -> TC Constrs
checkTerm ctx ty (V n) = do
    (r, ty') <- lookupName ctx n
    S.union ([r] <~ [Fixed R]) <$> conv ty ty'

checkTerm ctx (C TType) (Bind Pi r n ty tm)
    = checkTerm (add r n ty ctx) (C TType) tm

checkTerm ctx (Bind Pi r n ty tm) (Bind Lam r' n' ty' tm') = do
    xs <- conv ty ty'
    ys <- checkTerm (add r' n' ty ctx) tm tm'
    return $ S.unions [[r] <~ [r'], xs, ys]

checkTerm ctx ty (App r f x) = do
    argN <- freshN
    argTy <- V <$> freshN
    funConstrs <- checkTerm ctx (Bind Pi r argN argTy ty) f
    argConstrs <- checkTerm ctx argTy x
    return $ funConstrs `S.union` cond r argConstrs

checkTerm ctx ty (Case s sty alts) = do
    xs <- checkTerm ctx sty s
    ys <- S.unions <$> mapM (checkAlt ctx sty ty) alts
    return $ S.union xs ys

checkTerm ctx ty (Prim op) = conv ty (primType Fixed op)
checkTerm ctx ty (C c) = conv ty (constType c)
checkTerm ctx ty tm = throwE $ WrongType tm ty

checkAlt :: Ctx -> TTmeta -> TTmeta -> Alt Meta -> TC Constrs
checkAlt ctx sty bty (ConCase cn r ns tm) = do
    (r', cty) <- lookupName ctx cn
    (ctx', rty) <- augCtx ctx ns cty
    xs <- conv sty rty
    ys <- checkTerm ctx' bty tm
    return $ S.union xs ys

checkAlt ctx sty bty (ConstCase c tm) = do
    xs <- conv sty (constType c)
    ys <- checkTerm ctx bty tm
    return $ S.union xs ys

checkAlt ctx sty bty (DefaultCase tm) = checkTerm ctx bty tm

augCtx :: Ctx -> [Name] -> TTmeta -> TC (Ctx, TTmeta)
augCtx ctx [] ty = return (ctx, ty)
augCtx ctx (n : ns) (Bind Pi r n' ty tm) = augCtx (add r n ty ctx) ns tm
augCtx ctx (n : ns) ty = throwE $ BadCtorReturn ty
-}
