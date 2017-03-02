module Erasure.Prune where

import TT
import Pretty ()

pruneDef :: Def Relevance -> [Def ()]
pruneDef (Def n E ty body mcs) = []
-- special case for constructors to keep their arity:
pruneDef (Def n R ty (Abstract Postulate) mcs) = [Def n () (pruneTm ty) (Abstract Postulate) noConstrs]
pruneDef (Def n R ty body mcs) = [Def n () (V Blank) (pruneBody body) noConstrs]

pruneBody :: Body Relevance -> Body ()
pruneBody (Abstract a) = Abstract a
pruneBody (Term tm)    = Term $ pruneTm tm
pruneBody (Clauses cs) = Clauses $ map pruneClause cs

pruneClause :: Clause Relevance -> Clause ()
pruneClause (Clause pvs lhs rhs)
    = Clause
        (pruneDefs pvs)
        (pruneTm lhs)
        (pruneTm rhs)

pruneDefs :: [Def Relevance] -> [Def ()]
pruneDefs = concatMap pruneDef

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm (Bind b ds tm)
    = case pruneDefs ds of
        []  -> pruneTm tm
        ds' -> Bind b ds' (pruneTm tm)
pruneTm (App E f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Forced tm) = error $ "pruneTm: forced term: " ++ show tm
