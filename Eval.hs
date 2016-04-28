{-# LANGUAGE FlexibleContexts #-}
module Eval (eval) where

import TT
import Pretty
import Normalise
import qualified Data.Map as M

prog2tt :: Program r cs -> TT r
prog2tt (Prog defs) = defs2tt defs

defs2tt :: [Def r cs] -> TT r
defs2tt [] = V $ UN "main"
defs2tt (Def n r ty body cs : ds) = Bind Let (Def n r ty body Nothing) $ defs2tt ds

eval :: IsRelevance r => Form -> Program r cs -> TT r
eval form = red form M.empty . prog2tt
