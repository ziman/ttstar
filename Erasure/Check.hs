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
    | CantConvertAlt (Alt Meta) (Alt Meta)
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

cond :: Meta -> TC a -> TC a
cond m = censor $ S.map mogrify
  where
    mogrify (us :<-: gs) = us :<-: S.insert m gs

require :: Bool -> TCError -> TC ()
require True  _ = return ()
require False e = tcfail e

eq :: Meta -> Meta -> Constrs
eq r r' = S.unions [[r] <~ [r'], [r'] <~ [r]]

rename :: [Name] -> [Name] -> TTmeta -> TTmeta
rename [] [] tm = tm
rename (n : ns) (n' : ns') tm = rename ns ns' $ subst n (V n') tm
rename _ _ _ = error "rename: incoherent args"

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
convAlt x y = tcfail $ CantConvertAlt x y

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
    globals = M.fromList [(n, (r, ty)) | Def r n ty _ <- defs]

checkDef :: Ctx -> Def Meta -> TC ()
checkDef _ctx (Def _r _n _ty Ctor) = return ()
checkDef ctx (Def _r _n ty (Fun tm)) = conv ty =<< checkTm ctx tm

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
    xTy <- cond r $ checkTm ctx x
    case fTy of
        Bind Pi r' n' ty' tm' -> do
            tell (r `eq` r')
            conv ty' xTy
            return $ subst n' x tm'

        _ -> tcfail $ NonFunction f fTy

checkTm _ctx (Prim op) = return $ primType Fixed op

checkTm ctx t@(Case s alts) = do
    _sTy <- checkTm ctx s  -- we ignore scrutinee type
    alts' <- mapM (checkAlt ctx) alts
    return $ Case s alts'

checkTm _ctx (C c) = return $ constType c

checkTm _ctx Erased = return $ Erased

checkAlt :: Ctx -> Alt Meta -> TC (Alt Meta)
checkAlt ctx (DefaultCase tm) = DefaultCase <$> checkTm ctx tm
checkAlt ctx (ConstCase c tm) = ConstCase c <$> checkTm ctx tm
checkAlt ctx (ConCase cn r ns tm) = do
    (cr, cty) <- lookupName ctx cn
    tell (cr `eq` r)
    ctx' <- augCtx ctx ns cty
    ConCase cn r ns <$> checkTm ctx' tm
  where
    augCtx :: Ctx -> [Name] -> TTmeta -> TC Ctx
    augCtx ctx [] _ty = return ctx
    augCtx ctx (n : ns) (Bind Pi r _n' ty tm) = augCtx (add r n ty ctx) ns tm
    augCtx _ctx (_ : _ ) tm = tcfail $ BadCtorType tm
