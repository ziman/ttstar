module Erasure.Meta where

import TT
import Pretty
import Util.PrettyPrint

import Control.Applicative
import Control.Monad.Trans.State.Strict

data Meta = MVar Int | Fixed Relevance deriving (Eq, Ord)
type TTmeta = TT Meta
type MetaM = State Int

instance Show Meta where
    show (MVar  i) = "?" ++ show i
    show (Fixed r) = "!" ++ show r

instance PrettyR Meta where
    prettyCol x = colon <> showd x <> colon
    prettyApp x = text " -" <> showd x <> text "- "

meta :: Program (Maybe Relevance) VoidConstrs -> Program Meta VoidConstrs
meta prog = evalState (metaProg prog) 0

metaProg :: Program (Maybe Relevance) VoidConstrs -> MetaM (Program Meta VoidConstrs)
metaProg (Prog defs) = Prog <$> mapM metaDef defs

metaDef :: Def (Maybe Relevance) VoidConstrs -> MetaM (Def Meta VoidConstrs)
metaDef (Def n r ty mtm Nothing) = Def <$> pure n <*> freshM r <*> metaTm ty <*> metaBody mtm <*> pure Nothing

metaBody :: Maybe (TT (Maybe Relevance)) -> MetaM (Maybe (TT Meta))
metaBody  Nothing  = return $ Nothing
metaBody (Just tm) = Just <$> metaTm tm

freshM :: Maybe Relevance -> State Int Meta
freshM Nothing  = modify (+1) >> MVar <$> get
freshM (Just r) = return $ Fixed r

metaTm :: TT (Maybe Relevance) -> MetaM TTmeta
metaTm (V n) = return $ V n
metaTm (I n ty) = I n <$> metaTm ty
metaTm (Bind bnd n r ty tm) = Bind bnd <$> pure n <*> freshM r <*> metaTm ty <*> metaTm tm
metaTm (App r f x) = App <$> freshM r <*> metaTm f <*> metaTm x
metaTm (Let d tm) = Let <$> metaDef d <*> metaTm tm
metaTm (Case s alts) = Case <$> metaTm s <*> mapM metaAlt alts
metaTm Erased = return Erased
metaTm Type = return Type

metaAlt :: Alt (Maybe Relevance) -> MetaM (Alt Meta)
metaAlt (DefaultCase tm) = DefaultCase <$> metaTm tm
metaAlt (ConCase cn tm) = ConCase cn <$> metaTm tm
