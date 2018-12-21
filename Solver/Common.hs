module Solver.Common where

import TT.Core

import qualified Data.Map as M
import qualified Data.Set as S

toImpls :: Ord r => Constrs r -> M.Map (Guards r) (Uses r)
toImpls (Constrs impls eqs)
    = foldr union impls [eq r s | (r, s) <- S.toList eqs]
  where
    union = M.unionWith S.union
    eq r s = M.fromList
        [ (S.singleton r, S.singleton s)
        , (S.singleton s, S.singleton r)
        ]
