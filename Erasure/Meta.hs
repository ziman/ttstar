module Erasure.Meta where

import TT
import TTLens
import Pretty
import Util.PrettyPrint

import Control.Applicative
import Control.Monad.Trans.State.Strict

data Meta = MVar Int | Fixed Relevance deriving (Eq, Ord)
type TTmeta = TT Meta

instance Show Meta where
    show (MVar  i) = "?" ++ show i
    show (Fixed r) = "!" ++ show r

instance PrettyR Meta where
    prettyCol x = colon <> showd x <> colon
    prettyApp x = text " -" <> showd x <> text "- "

meta :: Program (Maybe Relevance) VoidConstrs -> Program Meta VoidConstrs
meta prog = evalState (progRelevance freshM prog) 0

freshM :: Maybe Relevance -> State Int Meta
freshM Nothing  = modify (+1) >> MVar <$> get
freshM (Just r) = return $ Fixed r
