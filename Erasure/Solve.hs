module Erasure.Solve where

import TTstar
import Erasure.Meta
import Erasure.Check

import qualified Data.Map as M
import qualified Data.Set as S

type CMap = M.Map Guards Uses

solve :: Constrs -> Uses
solve cs = step (S.singleton $ Fixed R) cmap
  where
    cmap = M.unionsWith S.union [M.singleton gs us | (us :<-: gs) <- S.toList cs]

step :: Uses -> CMap -> Uses
step ans cmap
    | S.null new = ans
    | otherwise = step (S.union ans new) prunedCmap
  where
    prunedCmap = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cmap
    new = M.findWithDefault S.empty S.empty prunedCmap
