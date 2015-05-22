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
solve = fst . forwardChain

reduce :: Constrs -> Constrs
reduce = snd . forwardChain

forwardChain :: Constrs -> (Uses, Constrs)
forwardChain = step $ S.singleton (Fixed R)

step :: Uses -> Constrs -> (Uses, Constrs)
step ans cs
    | S.null new = (ans, prunedCs)
    | otherwise = step ans' prunedCs
  where
    prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
    new = M.findWithDefault S.empty S.empty prunedCs_ans
    ans' = S.union ans new
    prunedCs = M.filterWithKey flt prunedCs_ans
    flt gs us = not (S.null gs) && not (S.null us)
