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
pruneDef (Def I _n _ty _dt) = []
pruneDef (Def R n _ty dt) = [Def () n Erased (pruneDefType dt)]

pruneDefType :: DefType Relevance -> DefType ()
pruneDefType  Axiom = Axiom
pruneDefType (Fun tm) = Fun $ pruneTm tm

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (Bind _bnd I _n _ty tm) = pruneTm tm
pruneTm (Bind bnd R n _ty tm) = Bind bnd () n Erased (pruneTm tm)
pruneTm (App I f _x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Case s alts) = Case (pruneTm s) (map pruneAlt alts)
pruneTm Erased = Erased
pruneTm Type = Type

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (DefaultCase tm) = DefaultCase $ pruneTm tm
pruneAlt (ConCase cn r tm) = ConCase cn () $ pruneTm tm  -- TODO
