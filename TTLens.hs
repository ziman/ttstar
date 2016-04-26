{-# LANGUAGE Rank2Types #-}
module TTLens where

import Data.Traversable
import Control.Applicative

import Lens.Family2.Unchecked

import TT

voidRelevance :: Traversal (VoidConstrs r) (cs' r') r r'
voidRelevance f _ = error "void elimination"

ttRelevance :: Traversal (TT r) (TT r') r r'
ttRelevance f = g
  where
    g tm = case tm of
        V n    -> pure $ V n
        I n ty -> I n <$> (g ty)
        Bind b d tm
            -> Bind b <$> defRelevance f d <*> g tm
        App r fun arg
            -> App <$> f r <*> g fun <*> g arg
        Forced tm -> Forced <$> g tm
        Erased -> pure Erased
        Type -> pure Type

defRelevance' :: Traversal (cs r) (cs' r') r r' -> Traversal (Def r cs) (Def r' cs') r r'
defRelevance' csRelevance f (Def n r ty body mcs)
    = Def n
        <$> f r
        <*> ttRelevance f ty
        <*> bodyRelevance f body
        <*> traverse (csRelevance f) mcs

bodyRelevance :: Traversal (Body r) (Body r') r r'
bodyRelevance f Abstract = pure Abstract
bodyRelevance f (Term tm) = Term <$> ttRelevance f tm
bodyRelevance f (Clauses cls) = Clauses <$> traverse (clauseRelevance f) cls

clauseRelevance :: Traversal (Clause r) (Clause r') r r'
clauseRelevance f (Clause pvs lhs rhs)
    = Clause <$> traverse (defRelevance f) pvs <*> ttRelevance f lhs <*> ttRelevance f rhs

defRelevance :: Traversal (Def r VoidConstrs) (Def r' cs') r r'
defRelevance = defRelevance' voidRelevance

progRelevance' :: Traversal (cs r) (cs' r') r r' -> Traversal (Program r cs) (Program r' cs') r r'
progRelevance' csRelevance f (Prog defs) = Prog <$> traverse (defRelevance' csRelevance f) defs

progRelevance :: Traversal (Program r VoidConstrs) (Program r' cs') r r'
progRelevance = progRelevance' voidRelevance
