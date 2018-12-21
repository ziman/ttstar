module Solver.Simple (solve, reduce) where

import TT.Core
import Erasure.Evar

import qualified Data.Map as M
import qualified Data.Set as S

reduce :: Constrs Evar -> Constrs Evar
reduce (Constrs impls eqs) = Constrs (reduceImpls impls) eqs  -- TODO

-- reduce the constraint set, keeping the empty-guard constraint
reduceImpls :: Impls Evar -> Impls Evar
reduceImpls impls
    | S.null (S.delete (Fixed R) us) = residue
    | otherwise = M.insert S.empty us residue
  where
    (us, residue) = solve impls

solve :: Impls Evar -> (Uses Evar, Impls Evar)
solve = step (S.singleton $ Fixed R)
  where
    step :: Uses Evar -> Impls Evar -> (Uses Evar, Impls Evar)
    step ans cs
        | S.null new = (ans, prunedCs)
        | otherwise = step (S.union ans new) prunedCs
      where
        prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
        new = M.findWithDefault S.empty S.empty prunedCs_ans
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null gs) && not (S.null us)
