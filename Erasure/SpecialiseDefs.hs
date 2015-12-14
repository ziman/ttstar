module Erasure.SpecialiseDefs (specialiseDefs) where

import TT
import TTLens
import Erasure.Meta
import Erasure.Solve

specialiseDefs :: Program Meta Constrs' -> Program Meta Constrs'
specialiseDefs (Prog defs) = Prog (concatMap specDef defs)

specDef :: Def Meta Constrs' -> [Def Meta Constrs']
specDef d = [d]
