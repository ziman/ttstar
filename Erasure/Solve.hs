module Erasure.Solve where

import TT
import Erasure.Meta

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

type Guards = S.Set Meta
type Uses = M.Map Meta Relevance
type Constrs = M.Map Guards Uses

-- reduce the constraint set, keeping the empty-guard constraint
reduce :: Constrs -> Constrs
reduce cs
    | M.null (M.delete (Fixed R) us) = residue
    | otherwise = M.insert S.empty us residue
  where
    (us, residue) = solve cs

solve :: Constrs -> (Uses, Constrs)
solve = step $ S.singleton (M.Map (Fixed R) R)
  where
    step :: Uses -> Constrs -> (Uses, Constrs)
    step ans cs
        | M.null new = (ans, prunedCs)
        | otherwise = step (ans `unionU` new) prunedCs
      where
        -- first, prune all guards by all metas mentioned in `ans`
        prunedCs_ans = M.mapKeysWith unionU (S.\\ M.keySet ans) $ cs

        -- then find out what's immediately deducible
        new = M.findWithDefault M.empty S.empty prunedCs_ans

        -- prune trivial implications
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null gs) && not (S.null us)

        unionU = M.unionWith lub
