module Erasure.Check where

import TT
import Reduce
import Erasure.Meta

import Control.Monad
import Control.Applicative
import Control.Arrow
import Control.Monad.Trans
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

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
    | CantMatch TTmeta TTmeta
    | Other String
    deriving (Eq, Ord, Show)

data TCFailure = TCFailure TCError [String]

instance Show TCFailure where
    show (TCFailure e []) = show e
    show (TCFailure e tb) = unlines (show e : "Traceback:" : zipWith (\i n -> show i ++ ". " ++ n) [1..] (reverse tb))

type TCState = Int
type TCTraceback = [String]
type TC a = ReaderT (TCTraceback, Ctx Meta) (WriterT Constrs (ExceptT TCFailure (State TCState))) a

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

rename :: [Name] -> [Name] -> TTmeta -> TTmeta
rename [] [] tm = tm
rename (n : ns) (n' : ns') tm = rename ns ns' $ subst n (V n') tm
rename _ _ _ = error "rename: incoherent args"

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
convAlt sty p@(ConCase cn r ar tm) q@(ConCase cn' r' ar' tm') = bt ("CONV-ALT", p, q) $ do
    require (cn == cn') $ Mismatch cn cn'
    require (ar == ar') $ Mismatch ("arity " ++ show ar) ("arity " ++ show ar')
    emit (r `eq` r')
    conv tm tm'
convAlt sty x y = tcfail $ CantConvertAlt x y

unPi :: TT Meta -> [(Name, Meta, TT Meta)] -> ([(Name, Meta, TT Meta)], TT Meta)
unPi (Bind Pi r n ty tm) args = unPi tm ((n, r, ty) : args)
unPi tm args = (args, tm)

uniformCase :: TTmeta -> [Alt Meta] -> TC ()
uniformCase  _ []     = return ()
uniformCase  x (a:as) = conv x (getTm a) >> uniformCase x as
  where
    getTm (DefaultCase tm) = tm
    getTm (ConCase _cn _r _ns tm) = tm

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

check :: Program Meta -> Either TCFailure Constrs
check prog = afterState
  where
    afterReader = runReaderT (checkProgram prog) ([], M.empty)
    afterWriter = execWriterT afterReader
    afterExcept = runExceptT  afterWriter
    afterState  = evalState   afterExcept 0

reduce' :: TT Meta -> TC (TT Meta)
reduce' tm = do
    (tb, ctx) <- ask
    return $ reduce ctx tm

checkProgram :: Program Meta -> TC ()
checkProgram (Prog defs) =
    local (const ([], globals))
        $ mapM_ checkDef defs
  where
    globals :: Ctx Meta
    globals = M.fromList $ map mkCtx defs
    
    mkCtx (Def r n ty Axiom) = (n, (r, ty, Nothing))
    mkCtx (Def r n ty (Fun tm)) = (n, (r, ty, Just tm))

checkDef :: Def Meta -> TC ()
checkDef (Def r n ty Axiom) = return ()
checkDef (Def r n ty (Fun tm)) = bt ("FUNDECL", n) $ do
    tmTy <- reduce' =<< checkTm tm
    ty' <- reduce' ty
    bt ("RET-TY", ty', tmTy) $ conv ty' tmTy

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
checkAlt (ConCase cn r arity tm) = bt ("CONCASE", cn, tm) $ do
    (cr, cty, _def) <- lookupName cn
    emit (cr `eq` r)
    ConCase cn r arity <$> checkTm tm
