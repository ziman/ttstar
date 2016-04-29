module Erasure.Prune where

import TT
import Pretty
import Control.Applicative
import qualified Data.Set as S

prune :: Program Relevance VoidConstrs -> Program () VoidConstrs
prune (Prog defs) = Prog $ concatMap pruneDef defs

pruneDef :: Def Relevance VoidConstrs -> [Def () VoidConstrs]
pruneDef (Def n E ty body mcs) = []
pruneDef (Def n R ty body mcs) = [Def n () Erased (pruneBody body) Nothing]

pruneBody :: Body Relevance -> Body ()
pruneBody (Abstract a)  = Abstract a
pruneBody (Term tm)     = Term $ pruneTm tm
pruneBody (Clauses cls) = Clauses $ map pruneClause cls

pruneClause :: Clause Relevance -> Clause ()
pruneClause (Clause pvs lhs rhs)
    = Clause
        (concatMap pruneDef pvs)
        (pruneLHS pvs $ pruneTm lhs)
        (pruneTm rhs)
  where

-- replace erased patvars with ____
pruneLHS :: [Def Relevance VoidConstrs] -> TT () -> TT ()
pruneLHS pvs lhs = foldr (\n -> subst n Erased) lhs elidedPVars
  where
    elidedPVars = S.fromList [n | Def n E _ _ _ <- pvs]

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm (Bind b (Def n E ty body cs) tm)
    = pruneTm tm
pruneTm (Bind b (Def n R ty body cs) tm)
    = Bind b (Def n () Erased (pruneBody body) Nothing) (pruneTm tm)
pruneTm (App E f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Forced t) = Forced $ pruneTm t
pruneTm Erased = Erased
pruneTm Type = Type
