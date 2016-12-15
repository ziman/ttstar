{-# LANGUAGE FlexibleContexts #-}
module Eval (eval) where

import TT
import Normalise

prog2tt :: Program r -> TT r
prog2tt (Prog defs) = defs2tt defs

defs2tt :: [Def r] -> TT r
defs2tt [] = V $ UN "main"
defs2tt (Def n r ty body cs : ds) = Bind Let [Def n r ty body noConstrs] $ defs2tt ds

eval :: IsRelevance r => Form -> Ctx r -> Program r -> TT r
eval form ctx = red form ctx . prog2tt
