{-# LANGUAGE Rank2Types #-}
module TTLens where

import qualified Data.Map as M
import qualified Data.Set as S

import Lens.Family2.Unchecked

import TT

ttRelevance :: Ord r' => Traversal (TT r) (TT r') r r'
ttRelevance f = g
  where
    g tm = case tm of
        V n    -> pure $ V n
        I n ty -> I n <$> g ty
        Bind b d tm
            -> Bind b <$> defRelevance f d <*> g tm
        App r fun arg
            -> App <$> f r <*> g fun <*> g arg
        Forced tm
            -> Forced <$> g tm

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
bodyRelevance f (Patterns cf) = Patterns <$> caseFunRelevance f cf

caseFunRelevance :: Ord r' => Traversal (CaseFun r) (CaseFun r') r r'
caseFunRelevance f (CaseFun args ct)
    = CaseFun
        <$> traverse (defRelevance f) args
        <*> caseTreeRelevance f ct

caseTreeRelevance :: Ord r' => Traversal (CaseTree r) (CaseTree r') r r'
caseTreeRelevance f (Leaf tm) = Leaf <$> ttRelevance f tm
caseTreeRelevance f (Case r s alts) = Case <$> f r <*> ttRelevance f s <*> traverse (altRelevance f) alts

altRelevance :: Ord r' => Traversal (Alt r) (Alt r') r r'
altRelevance f (Alt lhs rhs) = Alt <$> altLHSRelevance f lhs <*> caseTreeRelevance f rhs

altLHSRelevance :: Ord r' => Traversal (AltLHS r) (AltLHS r') r r'
altLHSRelevance f Wildcard = pure $ Wildcard
altLHSRelevance f (Ctor cn args eqs)
    = Ctor cn
        <$> traverse (defRelevance f) args
        <*> traverse (caseEqRelevance f) eqs

caseEqRelevance :: Ord r' => Traversal (Name, TT r) (Name, TT r') r r'
caseEqRelevance f (n, tm) = (,) n <$> ttRelevance f tm

progRelevance :: Ord r' => Traversal (Program r) (Program r') r r'
progRelevance f (Prog defs) = Prog <$> traverse (defRelevance f) defs

csRelevance :: Ord r' => Traversal (Constrs r) (Constrs r') r r'
csRelevance f = fmap M.fromList . traverse f' . M.toList
  where
    f' (x, y) = (,) <$> f'' x <*> f'' y
    f'' = fmap S.fromList . traverse f . S.toList

