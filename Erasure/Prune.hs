module Erasure.Prune where

import TT
import Pretty
import Control.Applicative

prune :: Program Relevance VoidConstrs -> Program () VoidConstrs
prune (Prog defs) = Prog $ concatMap pruneDef defs

pruneDef :: Def Relevance VoidConstrs -> [Def () VoidConstrs]
pruneDef (Def n E ty dt mcs) = []
pruneDef (Def n R ty dt mcs) = [Def n () Erased (pruneTm <$> dt) Nothing]

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (I n ty) = error $ "non-specialised instance found in pruneTm: " ++ show (n, ty)
pruneTm (Bind bnd n E ty tm) = pruneTm tm
pruneTm (Bind bnd n R ty tm) = Bind bnd n () Erased (pruneTm tm)
pruneTm (App E f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Let (Def n E ty mtm Nothing) tm) = pruneTm tm
pruneTm (Let (Def n R ty mtm Nothing) tm) = Let (Def n () Erased (pruneTm <$> mtm) Nothing) (pruneTm tm)
pruneTm (Case s _ty alts) = Case (pruneTm s) Nothing (map pruneAlt alts)
pruneTm Erased = Erased
pruneTm Type = Type

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (DefaultCase tm) = DefaultCase $ pruneTm tm
pruneAlt (ConCase cn tm) = ConCase cn $ pruneTm tm
