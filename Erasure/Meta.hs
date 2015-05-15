module Erasure.Meta where

import TTstar

import Control.Applicative
import Control.Monad.Trans.State.Strict

data Meta = MVar Int | Fixed Relevance deriving (Eq, Ord)
type TTmeta = TT' Meta
type MetaM = State Int

instance Show Meta where
    show (MVar i) = "?" ++ show i
    show (Fixed r) = "!" ++ show r

instance ShowR Meta where
    showR x = "[" ++ show x ++ "]"
    showX x = " -" ++ show x ++ "- "

meta :: Program (Maybe Relevance) -> Program Meta
meta prog = evalState (metaProg prog) 0

metaProg :: Program (Maybe Relevance) -> MetaM (Program Meta)
metaProg (Prog defs) = Prog <$> mapM metaDef defs

metaDef :: Def (Maybe Relevance) -> MetaM (Def Meta)
metaDef (Def r n ty dt) = Def <$> freshM r <*> pure n <*> metaTm ty <*> metaDefType dt

metaDefType :: DefType (Maybe Relevance) -> MetaM (DefType Meta)
metaDefType  Ctor    = return $ Ctor
metaDefType (Fun tm) = Fun <$> metaTm tm

freshM :: Maybe Relevance -> State Int Meta
freshM Nothing  = modify (+1) >> MVar <$> get
freshM (Just r) = return $ Fixed r

metaTm :: TT -> MetaM TTmeta
metaTm (V n) = return $ V n
metaTm (Bind bnd r n ty tm) = Bind bnd <$> freshM r <*> pure n <*> metaTm ty <*> metaTm tm
metaTm (App r f x) = App <$> freshM r <*> metaTm f <*> metaTm x
metaTm (Case s alts) = Case <$> metaTm s <*> mapM metaAlt alts
metaTm (Prim op) = return $ Prim op
metaTm (C c) = return $ C c

metaAlt :: Alt (Maybe Relevance) -> MetaM (Alt Meta)
metaAlt (DefaultCase tm) = DefaultCase <$> metaTm tm
metaAlt (ConCase cn tr ns tm) = ConCase cn <$> freshM tr <*> pure ns <*> metaTm tm
metaAlt (ConstCase c tm) = ConstCase c <$> metaTm tm
