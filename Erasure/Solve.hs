module Erasure.Solve where

import TT
import Erasure.Meta

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

type Guards = S.Set Meta
type Uses = M.Map Meta Relevance
type Metas = S.Set Meta
type Constrs = M.Map Guards Uses

unionU :: Uses -> Uses -> Uses
unionU = M.unionWith lub

-- reduce the constraint set, keeping the empty-guard constraint
reduce :: Constrs -> Constrs
reduce cs
    | M.null (M.delete (Fixed R) us) = residue
    | otherwise = M.insert S.empty us residue
  where
    (us, residue) = solve cs

solve :: Constrs -> (Uses, Constrs)
solve = step (S.singleton $ Fixed N) (S.singleton $ Fixed R)
  where
    step :: Metas -> Metas -> Constrs -> (Uses, Constrs)
    step ns rs cs
        | M.null newR && M.null newN
        = (M.fromList $ [(m,N)|m<-S.toList ns] ++ [(m,R)|m<-S.toList rs], prunedCs)

        | otherwise = step (S.union ns newNM) (S.union rs newRM) prunedCs
      where
        -- first, prune all guards by all metas known to be R
        prunedCs_R = M.mapKeysWith unionU (S.\\ rs) $ cs

        -- then find out what's immediately deducible as R
        newR = M.findWithDefault M.empty S.empty prunedCs_R

        -- then, prune the rest by all metas known to be N
        prunedCs_N = M.mapKeysWith unionU (S.\\ ns) $ prunedCs_R

        -- find out what's deducible as N
        newN = M.findWithDefault M.empty S.empty prunedCs_N

        -- construct the resulting R- and N-sets
        newRM = S.fromList [m | (m,R) <- M.toList newR]
        newNM = S.fromList $ [m | (m,N) <- M.toList newR] ++ [m | (m,_) <- M.toList newN]

        -- prune trivial implications
        prunedCs = M.filterWithKey flt prunedCs_N
        flt gs us = not (S.null gs) && not (M.null us)
