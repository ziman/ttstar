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
        Bind b n r ty tm
            -> Bind b n <$> f r <*> g ty <*> g tm
        App r fun arg
            -> App <$> f r <*> g fun <*> g arg
        Let def tm
            -> Let <$> defRelevance f def <*> g tm
        Case s alts
            -> Case <$> g s <*> traverse (altRelevance f) alts
        Erased -> pure Erased
        Type -> pure Type

defRelevance' :: Traversal (cs r) (cs' r') r r' -> Traversal (Def r cs) (Def r' cs') r r'
defRelevance' csRelevance f (Def n r ty mtm mcs)
    = Def n
        <$> f r
        <*> ttRelevance f ty
        <*> traverse (ttRelevance f) mtm
        <*> traverse (csRelevance f) mcs

defRelevance :: Traversal (Def r VoidConstrs) (Def r' cs') r r'
defRelevance = defRelevance' voidRelevance

altRelevance :: Traversal (Alt r) (Alt r') r r'
altRelevance f (ConCase cn tm) = ConCase cn <$> ttRelevance f tm
altRelevance f (DefaultCase tm) = DefaultCase <$> ttRelevance f tm

progRelevance' :: Traversal (cs r) (cs' r') r r' -> Traversal (Program r cs) (Program r' cs') r r'
progRelevance' csRelevance f (Prog defs) = Prog <$> traverse (defRelevance' csRelevance f) defs

progRelevance :: Traversal (Program r VoidConstrs) (Program r' cs') r r'
progRelevance = progRelevance' voidRelevance
