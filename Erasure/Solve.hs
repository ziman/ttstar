module Erasure.Solve where

import TT
import Erasure.Meta

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

type Guards = S.Set Meta
type Uses = (Metas, Metas)  -- N-uses, R-uses
type Metas = S.Set Meta
type Constrs = M.Map Guards Uses

unionU :: Uses -> Uses -> Uses
unionU (ns, rs) (ns', rs') =  (S.union ns ns', S.union rs rs')

nullU :: Uses -> Bool
nullU (ns, rs) = S.null ns && S.null (S.delete (Fixed R) rs)

-- reduce the constraint set, keeping the empty-guard constraint
reduce :: Constrs -> Constrs
reduce cs
    | nullU uncond = residue
    | otherwise = M.insert S.empty uncond residue
  where
    (uncond, residue) = solve cs

solve :: Constrs -> (Uses, Constrs)
solve = step (S.empty, S.singleton $ Fixed R)
  where
    step :: Uses -> Constrs -> (Uses, Constrs)
    step (ns, rs) cs
        | nullU (newN, newR) = ((ns, rs), prunedCs)
        | otherwise = step (S.union ns newN, S.union rs newR) prunedCs
      where
        -- first, prune all guards by all metas known to be R
        prunedCs_R = M.mapKeysWith unionU (S.\\ rs) $ cs

        -- then find out what's immediately deducible from R
        (newR_N, newR_R) = M.findWithDefault (S.empty, S.empty) S.empty prunedCs_R

        -- then, prune the rest by all metas known to be N
        prunedCs_N = M.mapKeysWith unionU (S.\\ ns) $ M.delete S.empty prunedCs_R

        -- find out what's deducible from N
        (newN_N, newN_R) = M.findWithDefault (S.empty, S.empty) S.empty prunedCs_N

        -- construct the resulting R- and N-sets
        newN = S.unions [newN_N, newN_R, newR_N] S.\\ ns
        newR = newR_R S.\\ rs

        -- prune trivial implications
        prunedCs = M.filterWithKey flt $ M.delete S.empty prunedCs_N
        flt gs us = not $ nullU us
