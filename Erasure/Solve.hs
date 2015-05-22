module Erasure.Solve where

import TT
import Erasure.Meta
import Erasure.Check

import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

type CMap = M.Map Guards Uses

solve :: Constrs -> Uses
solve = fst . reduce

reduce :: Constrs -> (Uses, Constrs)
reduce = second unCmap . step (S.singleton $ Fixed R) . mkCmap
  where
    mkCmap cs = M.unionsWith S.union [M.singleton gs us | (us :<-: gs) <- S.toList cs]
    unCmap cmap = S.fromList $ [us :<-: gs | (gs, us) <- M.toList cmap]

step :: Uses -> CMap -> (Uses, CMap)
step ans cmap
    | S.null new = (ans, cmap)
    | otherwise = step (S.union ans new) prunedCmap
  where
    prunedCmap = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cmap
    new = M.findWithDefault S.empty S.empty prunedCmap
