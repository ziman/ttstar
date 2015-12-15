module Erasure.SpecialiseDefs (specialiseDefs) where

import TT
import TTLens

import Erasure.Check (instantiate)
import Erasure.Meta
import Erasure.Solve

specialiseDefs :: Program Meta Constrs' -> Program Meta Constrs'
specialiseDefs (Prog defs) = Prog (concatMap specDef defs)

specDef :: Def Meta Constrs' -> [Def Meta Constrs']
specDef d@(Def n r ty mtm Nothing) = [d]  -- no constraints available -> monomorphic
specDef d@(Def n r ty Nothing mcs) = [d]  -- no body available -> monomorphic
specDef d@(Def n r ty (Just tm) (Just cs)) = [d]
