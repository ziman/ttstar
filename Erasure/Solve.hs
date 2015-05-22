module Erasure.Solve where

import TT
import Erasure.Meta

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

type Guards = S.Set Meta
type Uses = S.Set Meta
type Constrs = M.Map Guards Uses

-- reduce the constraint set, keeping the empty-guard constraint
reduce :: Constrs -> Constrs
reduce cs
    | S.null (S.delete (Fixed R) us) = residue
    | otherwise = M.insert S.empty us residue
  where
    (us, residue) = solve cs

solve :: Constrs -> (Uses, Constrs)
solve = step $ S.singleton (Fixed R)
  where
    step :: Uses -> Constrs -> (Uses, Constrs)
    step ans cs
        | S.null new = (ans, prunedCs)
        | otherwise = step (S.union ans new) prunedCs
      where
        prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
        new = M.findWithDefault S.empty S.empty prunedCs_ans
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null gs) && not (S.null us)
