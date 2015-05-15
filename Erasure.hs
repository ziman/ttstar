{-# LANGUAGE TupleSections #-}
module Erasure where

import Control.Applicative
import Control.Monad
import Control.Monad.Instances
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Except

import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import TTstar

data Meta = MVar Int | Fixed Relevance deriving (Eq, Ord, Show)
type TTmeta = TT' Meta
type MetaM = State Int

meta :: Program TT -> Program TTmeta
meta prog = evalState (metaProg prog) 0

metaProg :: Program TT -> MetaM (Program TTmeta)
metaProg = mapM metaDef

metaDef :: Def TT -> MetaM (Def TTmeta)
metaDef (Fun n ty tm) = Fun n <$> metaTm ty <*> metaTm tm

freshM :: Maybe Relevance -> State Int Meta
freshM Nothing  = modify (+1) >> MVar <$> get
freshM (Just r) = return $ Fixed r

metaTm :: TT -> MetaM TTmeta
metaTm (V n) = return $ V n
metaTm (Bind bnd r n ty tm) = Bind bnd <$> freshM r <*> pure n <*> metaTm ty <*> metaTm tm
metaTm (App r f x) = App <$> freshM r <*> metaTm f <*> metaTm x
metaTm (Case s sty alts) = Case <$> metaTm s <*> metaTm sty <*> mapM metaAlt alts
metaTm (Prim op) = return $ Prim op
metaTm (C c) = return $ C c

metaAlt :: Alt (Maybe Relevance) -> MetaM (Alt Meta)
metaAlt (DefaultCase tm) = DefaultCase <$> metaTm tm
metaAlt (ConCase cn tr ns tm) = ConCase cn <$> freshM tr <*> pure ns <*> metaTm tm
metaAlt (ConstCase c tm) = ConstCase c <$> metaTm tm

type Guards = S.Set Meta
type Uses = S.Set Meta
data Constr = Uses :<-: Guards deriving (Eq, Ord, Show)
type Constrs = S.Set Constr
type Ctx = M.Map Name (Meta, TTmeta)

data TCError
    = CantConvert TTmeta TTmeta
    | UnknownName Name
    | WrongType TTmeta TTmeta  -- term, type
    | BadCtorReturn TTmeta
    deriving (Eq, Ord, Show)

type TCState = Int
type TC a = ExceptT TCError (State TCState) a

cond :: Meta -> Constrs -> Constrs
cond m = S.map mogrify
  where
    mogrify (us :<-: gs) = us :<-: S.insert m gs

conv :: TTmeta -> TTmeta -> TC Constrs
conv tm tm' = return S.empty  -- this was checked by the typechecker

add :: Meta -> Name -> TTmeta -> Ctx -> Ctx
add r n ty = M.insert n (r, ty)

infix 3 <~
(<~) :: [Meta] -> [Meta] -> Constrs
us <~ gs = S.singleton (S.fromList us :<-: S.fromList gs)

steps :: [TC Constrs] -> TC Constrs
steps = fmap S.unions . sequence

freshN :: TC Name
freshN = do
    i <- lift $ get
    lift . put $ i+1
    return $ "_" ++ show i

lookupName :: Ctx -> Name -> TC (Meta, TTmeta)
lookupName ctx n
    | Just x <- M.lookup n ctx = return x
    | otherwise = throwE $ UnknownName n

check :: Program TTmeta -> Either TCError Constrs
check prog = evalState (runExceptT $ checkProgram prog) 0

checkProgram :: Program TTmeta -> TC Constrs
checkProgram prog = S.unions <$> mapM (checkDef globals) prog
  where
    globals :: Ctx
    globals = M.fromList [(dName d, (Fixed R, dType d)) | d <- prog]

checkDef :: Ctx -> Def TTmeta -> TC Constrs
checkDef ctx (Con cn ty)    = return S.empty
checkDef ctx (Fun fn ty tm) = checkTerm ctx ty tm

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
