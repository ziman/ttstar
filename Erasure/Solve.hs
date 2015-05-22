module Erasure.Solve where

import TT
import Erasure.Meta

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

type Guards = S.Set Meta
type Uses = S.Set Meta
type Constrs = M.Map Guards Uses

solve :: Constrs -> Uses
solve = fst . reduce

reduce :: Constrs -> (Uses, Constrs)
reduce = step $ S.singleton (Fixed R)

step :: Uses -> Constrs -> (Uses, Constrs)
step ans cs
    | S.null new = (ans, cs)
    | otherwise = step (S.union ans new) prunedCs
  where
    prunedCs = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
    new = M.findWithDefault S.empty S.empty prunedCs
