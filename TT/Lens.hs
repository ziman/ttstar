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
        V n     -> pure $ V n
        Meta i  -> pure $ Meta i
        EI n ty -> EI n <$> g ty
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
        PHead f
            -> pure $ PHead f

defRelevance :: Ord r' => Traversal (Def r) (Def r') r r'
defRelevance f (Def n r ty body)
    = Def n
        <$> f r
        <*> ttRelevance f ty
        <*> bodyRelevance f body

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

implRelevance :: Ord r' => Traversal (Impls r) (Impls r') r r'
implRelevance f = fmap M.fromList . traverse f' . M.toList
  where
    f' (x, y) = (,) <$> f'' x <*> f'' y
    f'' = fmap S.fromList . traverse f . S.toList

ttMetaNums :: Traversal' (TT r) Int
ttMetaNums f = ttMetas (\(Meta i) -> Meta <$> f i)

ttMetas :: Traversal' (TT r) (TT r)
ttMetas f = g
  where
    g tm@(V n)    = pure tm
    g tm@(Meta i) = f tm
    g (EI n ty)   = EI n <$> g ty
    g (Bind b ds tm) = Bind b <$> traverse (defMetas f) ds <*> g tm
    g (App r f x) = App r <$> g f <*> g x

defMetas :: Traversal' (Def r) (TT r)
defMetas f (Def n r ty body) = Def n r <$> ttMetas f ty <*> bodyMetas f body

bodyMetas :: Traversal' (Body r) (TT r)
bodyMetas f b@(Abstract _) = pure b
bodyMetas f (Term tm)      = Term <$> ttMetas f tm
bodyMetas f (Clauses cs)   = Clauses <$> traverse (clauseMetas f) cs

clauseMetas :: Traversal' (Clause r) (TT r)
clauseMetas f (Clause pvs lhs rhs) = Clause <$> traverse (defMetas f) pvs <*> patMetas f lhs <*> ttMetas f rhs

patMetas :: Traversal' (Pat r) (TT r)
patMetas f = g
  where
    g p@(PV _) = pure p
    g (PApp r f x) = PApp r <$> g f <*> g x
    g (PForced tm) = PForced <$> ttMetas f tm
    g p@(PHead f) = pure p
