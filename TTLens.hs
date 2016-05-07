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

defRelevance' :: Traversal (cs r) (cs' r') r r' -> Traversal (Def r cs) (Def r' cs') r r'
defRelevance' csRelevance f (Def n r ty body mcs)
    = Def n
        <$> f r
        <*> ttRelevance f ty
        <*> bodyRelevance f body
        <*> traverse (csRelevance f) mcs

bodyRelevance :: Traversal (Body r) (Body r') r r'
bodyRelevance f (Abstract a) = pure $ Abstract a
bodyRelevance f (Term tm) = Term <$> ttRelevance f tm
bodyRelevance f (Patterns cf) = Patterns <$> caseFunRelevance f cf

caseFunRelevance :: Traversal (CaseFun r) (CaseFun r') r r'
caseFunRelevance f (CaseFun args ct)
    = CaseFun
        <$> traverse (defRelevance f) args
        <*> caseTreeRelevance f ct

caseTreeRelevance :: Traversal (CaseTree r) (CaseTree r') r r'
caseTreeRelevance f (Leaf tm) = Leaf <$> ttRelevance f tm
caseTreeRelevance f (Case s alts) = Case <$> ttRelevance f s <*> traverse (altRelevance f) alts

altRelevance :: Traversal (Alt r) (Alt r') r r'
altRelevance f (Alt lhs rhs) = Alt <$> altLHSRelevance f lhs <*> caseTreeRelevance f rhs

altLHSRelevance :: Traversal (AltLHS r) (AltLHS r') r r'
altLHSRelevance f Wildcard = pure $ Wildcard
altLHSRelevance f (Ctor cn args eqs)
    = Ctor cn
        <$> traverse (defRelevance f) args
        <*> traverse (caseEqRelevance f) eqs

caseEqRelevance :: Traversal (Name, TT r) (Name, TT r') r r'
caseEqRelevance f (n, tm) = (,) n <$> ttRelevance f tm

defRelevance :: Traversal (Def r VoidConstrs) (Def r' cs') r r'
defRelevance = defRelevance' voidRelevance

progRelevance' :: Traversal (cs r) (cs' r') r r' -> Traversal (Program r cs) (Program r' cs') r r'
progRelevance' csRelevance f (Prog defs) = Prog <$> traverse (defRelevance' csRelevance f) defs

progRelevance :: Traversal (Program r VoidConstrs) (Program r' cs') r r'
progRelevance = progRelevance' voidRelevance
