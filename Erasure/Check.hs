module Erasure.Check where

import TTstar
import Reduce
import Erasure.Meta

import Control.Monad
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

import qualified Data.Map as M
import qualified Data.Set as S

type Ctx = Ctx' Meta
type Guards = S.Set Meta
type Uses = S.Set Meta
data Constr = Uses :<-: Guards deriving (Eq, Ord)
type Constrs = S.Set Constr

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

data TCFailure = TCFailure TCError [String] deriving (Show)

type TCState = Int
type TCCtx = [String]
type TC a = ReaderT TCCtx (WriterT Constrs (ExceptT TCFailure (State TCState))) a

cond :: Meta -> TC a -> TC a
cond m = mapReaderT $ censor (S.map mogrify)
  where
    mogrify (us :<-: gs) = us :<-: S.insert m gs

bt :: Show a => a -> TC b -> TC b
bt dbg = withReaderT (show dbg :)

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
    emit (r `eq` r')

conv (App r f x) (App r' f' x') = do
    conv f f'
    conv x x'
    emit (r `eq` r')

conv (Prim op) (Prim op') =
    require (op == op') $ Mismatch (show op) (show op')

conv (Case s alts) (Case s' alts') = do
    conv s s'
    require (length alts == length alts') $ Mismatch (show alts) (show alts')
    zipWithM_ convAlt alts alts'

conv (C c) (C c') =
    require (c == c') $ Mismatch (show c) (show c')

-- last-resort: uniform-case check
conv x@(Case _ _) y = conv y x
conv x (Case s alts) = uniformCase x alts

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
    emit (r `eq` r')
convAlt x y = tcfail $ CantConvertAlt x y

uniformCase :: TTmeta -> [Alt Meta] -> TC ()
uniformCase  _ []     = return ()
uniformCase  x (a:as) = conv x (getTm a) >> uniformCase x as
  where
    getTm (DefaultCase tm) = tm
    getTm (ConstCase _c tm) = tm
    getTm (ConCase _cn _r _ns tm) = tm

add :: Meta -> Name -> TTmeta -> Ctx -> Ctx
add r n ty = M.insert n (r, ty, Nothing)

infix 3 <~
(<~) :: [Meta] -> [Meta] -> Constrs
us <~ gs = S.singleton (S.fromList us :<-: S.fromList gs)

steps :: [TC Constrs] -> TC Constrs
steps = fmap S.unions . sequence

freshN :: TC Name
freshN = lift . lift . lift $ do
    i <- get
    put $ i+1
    return $ "_" ++ show i

tcfail :: TCError -> TC a
tcfail e = do
    bt <- ask
    lift . lift . throwE $ TCFailure e bt

emit :: Constrs -> TC ()
emit = lift . tell

lookupName :: Ctx -> Name -> TC (Meta, TTmeta, Maybe TTmeta)
lookupName ctx n
    | Just x <- M.lookup n ctx = return x
    | otherwise = tcfail $ UnknownName n

check :: Program Meta -> Either TCFailure Constrs
check prog = evalState (runExceptT . execWriterT $ runReaderT (checkProgram prog) []) 0

checkProgram :: Program Meta -> TC ()
checkProgram (Prog defs) = mapM_ (checkDef globals) defs
  where
    globals :: Ctx
    globals = M.fromList $ map mkCtx defs
    
    mkCtx (Def r n ty Ctor) = (n, (r, ty, Nothing))
    mkCtx (Def r n ty (Fun tm)) = (n, (r, ty, Just tm))

checkDef :: Ctx -> Def Meta -> TC ()
checkDef _ctx (Def _r _n _ty Ctor) = return ()
checkDef ctx (Def _r _n ty (Fun tm)) = conv ty =<< checkTm ctx tm

checkTm :: Ctx -> TTmeta -> TC TTmeta
checkTm ctx (V n) = do
    (r, ty, _def) <- lookupName ctx n
    emit ([r] <~ [Fixed R])
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
            emit (r `eq` r')
            conv ty' xTy
            return . reduce ctx $ subst n' x tm'

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
    (cr, cty, _def) <- lookupName ctx cn
    emit (cr `eq` r)
    ctx' <- augCtx ctx ns cty
    ConCase cn r ns <$> checkTm ctx' tm
  where
    augCtx :: Ctx -> [Name] -> TTmeta -> TC Ctx
    augCtx ctx [] _ty = return ctx
    augCtx ctx (n : ns) (Bind Pi r _n' ty tm) = augCtx (add r n ty ctx) ns tm
    augCtx _ctx (_ : _ ) tm = tcfail $ BadCtorType tm
