{-# LANGUAGE Rank2Types #-}
module TT.Lens where

import qualified Data.Map as M
import qualified Data.Set as S

import Lens.Family2.Unchecked

import TT.Core

ttRelevance :: Ord r' => Traversal (TT r) (TT r') r r'
ttRelevance f = g
  where
    g tm = case tm of
        V n    -> pure $ V n
        I n ty -> I n <$> g ty
        Bind b ds tm
            -> Bind b <$> traverse (defRelevance f) ds <*> g tm
        App r fun arg
            -> App <$> f r <*> g fun <*> g arg

patRelevance :: Ord r' => Traversal (Pat r) (Pat r') r r'
patRelevance f = g
  where
    g pat = case pat of
        PV n
            -> pure $ PV n
        PApp r fun arg
            -> PApp <$> f r <*> g fun <*> g arg
        PForced tm
            -> PForced <$> ttRelevance f tm
        PForcedCtor n
            -> pure $ PForcedCtor n

defRelevance :: Ord r' => Traversal (Def r) (Def r') r r'
defRelevance f (Def n r ty body mcs)
    = Def n
        <$> f r
        <*> ttRelevance f ty
        <*> bodyRelevance f body
        <*> csRelevance f mcs

bodyRelevance :: Ord r' => Traversal (Body r) (Body r') r r'
bodyRelevance f (Abstract a) = pure $ Abstract a
bodyRelevance f (Term tm) = Term <$> ttRelevance f tm
bodyRelevance f (Clauses cs) = Clauses <$> traverse (clauseRelevance f) cs

clauseRelevance :: Ord r' => Traversal (Clause r) (Clause r') r r'
clauseRelevance f (Clause pvs lhs rhs)
    = Clause
        <$> traverse (defRelevance f) pvs
        <*> patRelevance f lhs
        <*> ttRelevance f rhs

csRelevance :: Ord r' => Traversal (Constrs r) (Constrs r') r r'
csRelevance f = fmap M.fromList . traverse f' . M.toList
  where
    f' (x, y) = (,) <$> f'' x <*> f'' y
    f'' = fmap S.fromList . traverse f . S.toList
