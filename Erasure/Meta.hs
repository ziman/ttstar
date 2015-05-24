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
    show (MVar i j) = "?" ++ show i ++ "_" ++ show j
    show (Fixed r) = "!" ++ show r

instance PrettyR Meta where
    prettyCol x = colon <> showd x <> colon
    prettyApp x = text " -" <> showd x <> text "- "

meta :: Program (Maybe Relevance) Void -> Program Meta Void
meta prog = evalState (metaProg prog) 0

metaProg :: Program (Maybe Relevance) Void -> MetaM (Program Meta Void)
metaProg (Prog defs) = Prog <$> mapM metaDef defs

metaDef :: Def (Maybe Relevance) Void -> MetaM (Def Meta Void)
metaDef (Def n r ty mtm cs) = Def <$> pure n <*> freshM r <*> metaTm ty <*> metaBody mtm <*> pure cs

metaBody :: Maybe (TT (Maybe Relevance)) -> MetaM (Maybe (TT Meta))
metaBody  Nothing  = return $ Nothing
metaBody (Just tm) = Just <$> metaTm tm

freshM :: Maybe Relevance -> State Int Meta
freshM Nothing  = modify (+1) >> MVar <$> get <*> pure 0
freshM (Just r) = return $ Fixed r

metaTm :: TT (Maybe Relevance) -> MetaM TTmeta
metaTm (V n) = return $ V n
metaTm (Bind bnd n r ty tm) = Bind bnd <$> pure n <*> freshM r <*> metaTm ty <*> metaTm tm
metaTm (App pi_r r f x) = App <$> freshM pi_r <*> freshM r <*> metaTm f <*> metaTm x
metaTm (Case s alts) = Case <$> metaTm s <*> mapM metaAlt alts
metaTm Erased = return Erased
metaTm Type = return Type

metaAlt :: Alt (Maybe Relevance) -> MetaM (Alt Meta)
metaAlt (DefaultCase tm) = DefaultCase <$> metaTm tm
metaAlt (ConCase cn tm) = ConCase cn <$> metaTm tm
