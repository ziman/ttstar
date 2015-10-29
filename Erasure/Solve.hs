module Erasure.Solve where

import TT
import Erasure.Meta

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

type Guards = S.Set Meta
type MetaSet = S.Set Meta
type Uses = M.Map Meta Relevance
type Constrs = M.Map Guards Uses

-- reduce the constraint set, keeping the empty-guard constraint
reduce :: Constrs -> Constrs
reduce cs
    | S.null (S.delete (Fixed R) us) = residue
    | otherwise = M.insert S.empty us residue
  where
    (us, residue) = solve cs

solve :: Constrs -> (MetaSet, MetaSet, Constrs)
solve cs = step (S.singleton $ Fixed P) (S.singleton $ Fixed K) cs
  where
    step :: MetaSet -> MetaSet -> Constrs -> (MetaSet, MetaSet, Constrs)
    step ps ks cs
        | S.null new = (ans, prunedCs)
        | otherwise = step (S.union ans new) prunedCs
      where
        prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
        new = M.findWithDefault S.empty S.empty prunedCs_ans
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null gs) && not (S.null us)
