module Erasure.SpecialiseDefs (specialiseDefs) where

import TT
import TTLens

import Erasure.Check (instantiate)
import Erasure.Meta
import Erasure.Solve

specialiseDefs :: Program Meta VoidConstrs -> Program Meta VoidConstrs
specialiseDefs (Prog defs) = Prog (concatMap specDef defs)

specDef :: Def Meta VoidConstrs -> [Def Meta VoidConstrs]
specDef d@(Def n r ty mtm Nothing) = [d]
