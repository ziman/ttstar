module Erasure.Evar where

import TT
import TTLens
import Pretty
import Util.PrettyPrint

import Lens.Family2
import Control.Monad.Trans.State.Strict

data Evar = MVar Int | Fixed Relevance deriving (Eq, Ord)
type TTevar = TT Evar

instance Show Evar where
    show (MVar  i) = show i
    show (Fixed r) = show r

instance ShowUnicode Evar where
    showUnicode = text . map sup . show

instance PrettyR Evar where
    prettyCol x
        | useUnicode = colon <> showUnicode x
        | otherwise  = colon <> showd x <> colon

    prettyApp x
        | useUnicode = text " " <> showUnicode x <> text " "
        | otherwise  = text " -" <> showd x <> text "- "

    prettyAlt (Fixed r) = Just (showd r)
    prettyAlt (MVar i) = Just (showd i)

evar :: Program (Maybe Relevance) -> Program Evar
evar prog = evalState (ttRelevance freshM prog) 0

freshM :: Maybe Relevance -> State Int Evar
freshM Nothing  = modify (+1) >> MVar <$> get
freshM (Just r) = return $ Fixed r

evarsOccurIn :: Program Evar -> Bool
evarsOccurIn prog = any isEvar (prog ^.. (ttRelevance :: Traversal' (TT Evar) Evar))
  where
    isEvar (MVar  _) = True
    isEvar (Fixed _) = False
