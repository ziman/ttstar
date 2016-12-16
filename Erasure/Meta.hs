module Erasure.Meta where

import TT
import TTLens
import Pretty
import Util.PrettyPrint

import Control.Monad.Trans.State.Strict

data Meta = MVar Int | Fixed Relevance deriving (Eq, Ord)
type TTmeta = TT Meta

instance Show Meta where
    show (MVar  i) = show i
    show (Fixed r) = show r

instance ShowUnicode Meta where
    showUnicode = text . map sup . show

instance PrettyR Meta where
    prettyCol x
        | useUnicode = colon <> showUnicode x
        | otherwise  = colon <> showd x <> colon

    prettyApp x
        | useUnicode = text " " <> showUnicode x <> text " "
        | otherwise  = text " -" <> showd x <> text "- "

    prettyAlt (Fixed r) = Just (showd r)
    prettyAlt (MVar i) = Just (showd i)

meta :: Program (Maybe Relevance) -> Program Meta
meta prog = evalState (ttRelevance freshM prog) 0

freshM :: Maybe Relevance -> State Int Meta
freshM Nothing  = modify (+1) >> MVar <$> get
freshM (Just r) = return $ Fixed r
