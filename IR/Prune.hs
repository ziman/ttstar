module IR.Prune (pruneIR) where

import IR.Core
import qualified Data.Set as S

pruneIR :: IR -> IR
pruneIR = fst . pruneTm

pruneTm :: IR -> (IR, S.Set IName)

pruneTm (IV n) = (IV n, S.singleton n)

pruneTm (ILam n rhs) = (ILam n rhs', S.delete n rhsNs)
  where
    (rhs', rhsNs) = pruneTm rhs

pruneTm (IApp f x) = (IApp f' x', S.union fNs xNs)
  where
    (f', fNs) = pruneTm f
    (x', xNs) = pruneTm x

pruneTm (ILet n (IConstructor arity) rhs) = (ILet n (IConstructor arity) rhs', S.delete n rhsNs)
  where
    (rhs', rhsNs) = pruneTm rhs

pruneTm (ILet n (IForeign code) rhs) = (ILet n (IForeign code) rhs', S.delete n rhsNs)
  where
    (rhs', rhsNs) = pruneTm rhs

pruneTm (ILet n (ICaseFun vs ct) rhs) = (ILet n (ICaseFun vs ct') rhs', ns)
  where
    deletedNames = S.fromList (n : map IPV vs)
    ns = S.union rhsNs ctNs S.\\ deletedNames
    (rhs', rhsNs) = pruneTm rhs
    (ct', ctNs) = pruneCT ct

pruneTm (IError msg) = (IError msg, S.empty)

pruneCT :: ICaseTree -> (ICaseTree, S.Set IName)
pruneCT (ILeaf rhs) = (ILeaf rhs', rhsNs)
  where
    (rhs', rhsNs) = pruneTm rhs

pruneCT (ICase v [IDefault ct]) = (ICase v [IDefault ct'], S.insert (IPV v) ctNs)
  where
    (ct', ctNs) = pruneCT ct

pruneCT (ICase v [ICtor cn vs ct])
    | S.null (S.intersection vsS ctNs)
    = (ct', ctNs')

    | otherwise
    = (ICase v [ICtor cn vs ct'], S.insert (IPV v) ctNs')
  where
    vsS = S.fromList $ map IPV vs
    ctNs' = ctNs S.\\ vsS
    (ct', ctNs) = pruneCT ct

pruneCT (ICase v alts)
    = ( ICase v $ map fst alts'
      , S.insert (IPV v) . S.unions $ map snd alts'
      )
  where
    alts' = map pruneAlt alts

pruneAlt :: IAlt -> (IAlt, S.Set IName)
pruneAlt (IDefault ct) = (IDefault ct', ctNs)
  where
    (ct', ctNs) = pruneCT ct

pruneAlt (ICtor cn vs ct) = (ICtor cn vs ct', ctNs')
  where
    vsS = S.fromList $ map IPV vs
    ctNs' = ctNs S.\\ vsS
    (ct', ctNs) = pruneCT ct

