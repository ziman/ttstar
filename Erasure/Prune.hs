module Erasure.Prune where

import TT
import Pretty
import Control.Applicative
import qualified Data.Set as S

prune :: Program Relevance VoidConstrs -> Program () VoidConstrs
prune (Prog defs) = Prog $ concatMap (pruneDef eds) defs
  where
    -- elided defs
    eds = S.fromList [n | Def n E _ _ _ <- defs]

pruneDef :: S.Set Name -> Def Relevance VoidConstrs -> [Def () VoidConstrs]
pruneDef eds (Def n E ty body mcs) = []
pruneDef eds (Def n R ty body mcs) = [Def n () (V Blank) (pruneBody eds body) Nothing]

pruneBody :: S.Set Name -> Body Relevance -> Body ()
pruneBody eds (Abstract a)  = Abstract a
pruneBody eds (Term tm)     = Term $ pruneTm eds tm
pruneBody eds (Clauses cls) = Clauses $ concatMap (pruneClause eds) cls

pruneClause :: S.Set Name -> Clause Relevance -> [Clause ()]

-- remove all clauses that refer to erased postulates
-- those clauses can never be matched because those postulates are never instantiated
pruneClause eds (Clause pvs lhs rhs)
    | or [lhs `refersTo` n | n <- S.toList eds]
    = []

pruneClause eds (Clause pvs lhs rhs)
    = [Clause
        (concatMap (pruneDef eds) pvs)
        (pruneLHS epvs $ pruneTm eds lhs)
        (pruneTm eds rhs)]
  where
    -- elided patvars
    epvs = S.fromList [n | Def n E _ _ _ <- pvs]

-- replace erased patvars with ____
-- remove clauses mentioning elided defs on the LHS
pruneLHS :: S.Set Name -> TT () -> TT ()
pruneLHS epvs lhs = foldr (\n -> subst n (V Blank)) lhs (S.toList epvs)

pruneTm :: S.Set Name -> TT Relevance -> TT ()
pruneTm eds (V n) = V n
pruneTm eds (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm eds (Bind b d tm)
    = case pruneDef eds d of
        []   -> pruneTm eds tm
        [d'] -> Bind b d' (pruneTm eds tm)
pruneTm eds (App E f x) = pruneTm eds f
pruneTm eds (App R f x) = App () (pruneTm eds f) (pruneTm eds x)
pruneTm eds (Forced t) = Forced $ pruneTm eds t
pruneTm eds Type = Type
