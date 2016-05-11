module Erasure.Prune where

import TT
import Pretty
import Control.Applicative
import qualified Data.Set as S

prune :: Program Relevance VoidConstrs -> Program () VoidConstrs
prune (Prog defs) = Prog $ pruneDefs defs

pruneDef :: Def Relevance VoidConstrs -> [Def () VoidConstrs]
pruneDef (Def n E ty body mcs) = []
pruneDef (Def n R ty body mcs) = [Def n () (V Blank) (pruneBody body) Nothing]

pruneBody :: Body Relevance -> Body ()
pruneBody (Abstract a)  = Abstract a
pruneBody (Term tm)     = Term $ pruneTm tm
pruneBody (Patterns cf) = Patterns $ pruneCaseFun cf

pruneCaseFun :: CaseFun Relevance -> CaseFun ()
pruneCaseFun (CaseFun args ct)
    = CaseFun (pruneDefs args) (pruneCaseTree ct)

pruneCaseTree :: CaseTree Relevance -> CaseTree ()
pruneCaseTree (Leaf tm) = Leaf $ pruneTm tm
pruneCaseTree (Case E s [Alt lhs rhs]) = pruneCaseTree rhs
pruneCaseTree (Case R s alts) = Case () (pruneTm s) $ map pruneAlt alts
pruneCaseTree t@(Case E s alts) = error $ "trying to prune non-singleton tree: " ++ show t

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (Alt lhs rhs) = Alt (pruneAltLHS lhs) (pruneCaseTree rhs)

pruneAltLHS :: AltLHS Relevance -> AltLHS ()
pruneAltLHS Wildcard = Wildcard
pruneAltLHS (Ctor cn args eqs)
    = Ctor cn (pruneDefs args) [(n, pruneTm tm) | (n, tm) <- eqs]

pruneDefs :: [Def Relevance VoidConstrs] -> [Def () VoidConstrs]
pruneDefs = concatMap pruneDef

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm (Bind b d tm)
    = case pruneDef d of
        []   -> pruneTm tm
        [d'] -> Bind b d' (pruneTm tm)
pruneTm (App E f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
