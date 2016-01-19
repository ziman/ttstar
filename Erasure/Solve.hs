{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Erasure.Solve where

import TT
import Erasure.Meta

import Data.Traversable (traverse)
import Control.Applicative
import Control.Arrow (second)
import qualified Data.Map as M
import qualified Data.Set as S

import TTLens
import Lens.Family2

import Debug.Trace

type Guards'  r = S.Set r
type Uses'    r = S.Set r
newtype Constrs' r = CS { runCS :: M.Map (Guards' r) (Uses' r) }

class CsRelevance cs where
    csRelevance :: (Ord r, Ord r') => Traversal (cs r) (cs r') r r'

instance CsRelevance Constrs' where
    csRelevance f = fmap (CS . M.fromList) . traverse f' . M.toList . runCS
      where
        f' (x, y) = (,) <$> f'' x <*> f'' y
        f'' = fmap S.fromList . traverse f . S.toList

instance CsRelevance VoidConstrs where
    csRelevance f = voidElim . getConst

type Guards  = Guards'  Meta
type Uses    = Uses'    Meta
type Constrs = Constrs' Meta

-- reduce the constraint set, keeping the empty-guard constraint
reduce :: Constrs -> Constrs
reduce cs
    | S.null (S.delete (Fixed R) us) = residue
    | otherwise = (CS . M.insert S.empty us . runCS) residue
  where
    (us, residue) = solve cs

solve :: Constrs -> (Uses, Constrs)
solve = step $ S.singleton (Fixed R)
  where
    step :: Uses -> Constrs -> (Uses, Constrs)
    step ans (CS cs)
        | S.null new = (ans, CS prunedCs)
        | otherwise = step (S.union ans new) (CS prunedCs)
      where
        prunedCs_ans = M.mapKeysWith S.union (S.\\ ans) . M.map (S.\\ ans) $ cs
        new = M.findWithDefault S.empty S.empty prunedCs_ans
        prunedCs = M.filterWithKey flt prunedCs_ans
        flt gs us = not (S.null gs) && not (S.null us)
