module Erasure.Prune where

import TT
import Pretty ()

prune :: Program Relevance -> Program ()
prune (Prog defs) = Prog $ pruneDefs defs

pruneDef :: Def Relevance -> [Def ()]
pruneDef (Def n E ty body mcs) = []
pruneDef (Def n R ty body mcs) = [Def n () (V Blank) (pruneBody body) noConstrs]

pruneBody :: Body Relevance -> Body ()
pruneBody (Abstract a)  = Abstract a
pruneBody (Term tm)     = Term $ pruneTm tm
pruneBody (Patterns cf) = 
    case pruneCaseFun cf of
        CaseFun [] (Leaf tm) -> Term tm
            -- ^^ makes stuff neater
            -- there's a bug in normalisation somewhere that doesn't reduce
            -- zero-arg CaseFuns. Let's just clean it here.

        cf' -> Patterns cf'

pruneCaseFun :: CaseFun Relevance -> CaseFun ()
pruneCaseFun (CaseFun args ct)
    = CaseFun (pruneDefs args) (pruneCaseTree ct)

pruneCaseTree :: CaseTree Relevance -> CaseTree ()
pruneCaseTree (Leaf tm) = Leaf $ pruneTm tm
pruneCaseTree (Case E s [Alt lhs rhs]) = pruneCaseTree rhs
pruneCaseTree (Case R s alts) = Case () (pruneTm s) $ concatMap pruneAlt alts
pruneCaseTree t@(Case E s alts) = error $ "trying to prune non-singleton tree: " ++ show t

pruneAlt :: Alt Relevance -> [Alt ()]
pruneAlt (Alt Wildcard rhs) = [Alt Wildcard $ pruneCaseTree rhs]
pruneAlt (Alt (Ctor E cn args eqs) rhs) = []
pruneAlt (Alt (Ctor R cn args eqs) rhs)
    = [Alt (Ctor () cn (pruneDefs args) []) (pruneCaseTree rhs)]

pruneDefs :: [Def Relevance] -> [Def ()]
pruneDefs = concatMap pruneDef

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm (Bind b d tm)
    = case pruneDef d of
        []   -> pruneTm tm
        [d'] -> Bind b d' (pruneTm tm)
        _    -> error "pruneTm: impossible def prune"
pruneTm (App E f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Forced tm) = error $ "pruneTm: forced term: " ++ show tm
