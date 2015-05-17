module Erasure.Meta where

import TT
import Pretty
import Util.PrettyPrint

import Control.Applicative
import Control.Monad.Trans.State.Strict

data Meta = MVar Int Int | Fixed Relevance deriving (Eq, Ord)
type TTmeta = TT Meta
type MetaM = State Int

instance Show Meta where
    show (MVar i 0) = "?" ++ show i
    show (MVar i j) = "?" ++ show i ++ "/" ++ show j
    show (Fixed r) = "!" ++ show r

instance PrettyR Meta where
    prettyCol x = colon <> showd x <> colon
    prettyApp x = text " -" <> showd x <> text "- "

meta :: Program (Maybe Relevance) -> Program Meta
meta prog = evalState (metaProg prog) 0

metaProg :: Program (Maybe Relevance) -> MetaM (Program Meta)
metaProg (Prog defs) = Prog <$> mapM metaDef defs

metaDef :: Def (Maybe Relevance) -> MetaM (Def Meta)
metaDef (Def r n ty dt) = Def <$> freshM r <*> pure n <*> metaTm ty <*> metaDefType dt

metaDefType :: DefType (Maybe Relevance) -> MetaM (DefType Meta)
metaDefType  Axiom   = return $ Axiom
metaDefType (Fun tm) = Fun <$> metaTm tm

freshM :: Maybe Relevance -> State Int Meta
freshM Nothing  = modify (+1) >> MVar <$> get <*> pure 0
freshM (Just r) = return $ Fixed r

metaTm :: TT MRel -> MetaM TTmeta
metaTm (V n) = return $ V n
metaTm (Bind bnd r n ty tm) = Bind bnd <$> freshM r <*> pure n <*> metaTm ty <*> metaTm tm
metaTm (App r f x) = App <$> freshM r <*> metaTm f <*> metaTm x
metaTm (Case s alts) = Case <$> metaTm s <*> mapM metaAlt alts
metaTm Erased = return Erased
metaTm Type = return Type

metaAlt :: Alt (Maybe Relevance) -> MetaM (Alt Meta)
metaAlt (DefaultCase tm) = DefaultCase <$> metaTm tm
metaAlt (ConCase cn tr ns tm) = ConCase cn <$> freshM tr <*> pure ns <*> metaTm tm

-- Polymorphism
-- differently-typed case alts
