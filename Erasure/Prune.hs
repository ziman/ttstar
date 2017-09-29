module Erasure.Prune where

import TT.Core  
import TT.Pretty ()
import qualified Data.Map as M

pruneDef :: Def Relevance -> [Def ()]
pruneDef (Def n E ty body mcs) = []
-- special case for constructors and postulates to keep their arity:
pruneDef (Def n R ty (Abstract Constructor) mcs) = [Def n () (pruneTm ty) (Abstract Constructor) noConstrs]
pruneDef (Def n R ty (Abstract Postulate) mcs) = [Def n () (pruneTm ty) (Abstract Postulate) noConstrs]
pruneDef (Def n R ty body mcs) = [Def n () (V Blank) (pruneBody body) noConstrs]

pruneBody :: Body Relevance -> Body ()
pruneBody (Abstract a) = Abstract a
pruneBody (Term tm)    = Term $ pruneTm tm
pruneBody (Clauses cs) =
    case map pruneClause cs of
        [Clause [] (PForced _) rhs] -> Term rhs
        cs' -> Clauses cs'

pruneClause :: Clause Relevance -> Clause ()
pruneClause (Clause pvs lhs rhs)
    = Clause
        (pruneDefs pvs)
        (prunePat (M.fromList [(defName d, d) | d <- pvs]) lhs)
        (pruneTm rhs)

pruneDefs :: [Def Relevance] -> [Def ()]
pruneDefs = concatMap pruneDef

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (EI n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm (Bind b ds tm)
    = case pruneDefs ds of
        []  -> pruneTm tm
        ds' -> Bind b ds' (pruneTm tm)
pruneTm (App E f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)

prunePat :: Ctx Relevance -> Pat Relevance -> Pat ()
prunePat pvs (PV n)
    = case defR <$> M.lookup n pvs of
        Just R  -> PV n  -- relevant patvar
        Just E  -> PV Blank  -- irrelevant patvar
        Nothing -> PV n  -- constructor
prunePat pvs (PApp E f x) = prunePat pvs f
prunePat pvs (PApp R f x) = PApp () (prunePat pvs f) (prunePat pvs x)
prunePat pvs (PForced tm) = PForced $ V Blank
