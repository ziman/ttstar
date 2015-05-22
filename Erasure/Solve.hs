module Erasure.Solve where

import TT
import Erasure.Meta

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

type Guards = S.Set Meta
type Uses = S.Set Meta
type Constrs = M.Map Guards Uses

-- reduce the constraint set, keeping the empty-guard constraint
reduce :: Constrs -> Constrs
reduce = step $ S.singleton (Fixed R)
  where
    step :: Uses -> Constrs -> Constrs
    step ans cs
        | S.null new = prunedCs
        | otherwise = step (S.union ans new) prunedCs
      where
        prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
        new = M.findWithDefault S.empty S.empty prunedCs_ans S.\\ ans
        ans' = S.union ans new
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null us)

solve :: Constrs -> Uses
solve = step $ S.singleton (Fixed R)
  where
    step :: Uses -> Constrs -> Uses
    step ans cs
        | S.null new = ans
        | otherwise = step (S.union ans new) prunedCs
      where
        prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
        new = M.findWithDefault S.empty S.empty prunedCs_ans
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null gs) && not (S.null us)
