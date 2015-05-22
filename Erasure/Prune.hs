module Erasure.Prune where

import TT
import Erasure.Meta
import Erasure.Check
import Erasure.Solve

import qualified Data.Set as S

annotate :: Uses -> Program Meta -> Program Relevance
annotate uses = fmap rel
  where
    rel m
        | m `S.member` uses = R
        | otherwise         = I

prune :: Program Relevance -> Program ()
prune (Prog defs) = Prog $ concatMap pruneDef defs

pruneDef :: Def Relevance -> [Def ()]
pruneDef (Def n I ty dt) = []
pruneDef (Def n R ty dt) = [Def n () Erased (pruneDefType dt)]

pruneDefType :: DefType Relevance -> DefType ()
pruneDefType  Axiom = Axiom
pruneDefType (Fun tm) = Fun $ pruneTm tm

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (Bind bnd n I ty tm) = pruneTm tm
pruneTm (Bind bnd n R ty tm) = Bind bnd n () Erased (pruneTm tm)
pruneTm (App I f x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Case s alts) = Case (pruneTm s) (map pruneAlt alts)
pruneTm Erased = Erased
pruneTm Type = Type

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (DefaultCase tm) = DefaultCase $ pruneTm tm
pruneAlt (ConCase cn r tm) = ConCase cn () $ pruneTm tm
