module Erasure.SolveIndexed (solveIndexed) where

import TT.Core
import Erasure.Evar

import qualified Data.Map as M
import qualified Data.Set as S

solveIndexed :: Constrs Evar -> (Uses Evar, Constrs Evar)
solveIndexed = step $ S.singleton (Fixed R)
  where
    step :: Uses Evar -> Constrs Evar -> (Uses Evar, Constrs Evar)
    step ans cs
        | S.null new = (ans, prunedCs)
        | otherwise = step (S.union ans new) prunedCs
      where
        prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
        new = M.findWithDefault S.empty S.empty prunedCs_ans
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null gs) && not (S.null us)
