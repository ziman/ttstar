module Erasure.Prune where

import TTstar
import Erasure.Meta
import Erasure.Check

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
pruneDef (Def R n ty dt) = [Def () n (pruneTm ty) (pruneDefType dt)]

pruneDefType :: DefType Relevance -> DefType ()
pruneDefType Ctor = Ctor
pruneDefType (Fun tm) = Fun $ pruneTm tm

pruneTm :: TT' Relevance -> TT' ()
pruneTm (V n) = V n
pruneTm (Bind _bnd I _n _ty tm) = pruneTm tm
pruneTm (Bind bnd R n ty tm) = Bind bnd () n (pruneTm ty) (pruneTm tm)
pruneTm (App I f _x) = pruneTm f
pruneTm (App R f x) = App () (pruneTm f) (pruneTm x)
pruneTm (Prim op) = Prim op
pruneTm (Case s alts) = Case (pruneTm s) (map pruneAlt alts)
pruneTm (C c) = C c

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (DefaultCase tm) = DefaultCase $ pruneTm tm
pruneAlt (ConstCase c tm) = ConstCase c $ pruneTm tm
pruneAlt (ConCase cn _r ns tm) = ConCase cn () ns $ pruneTm tm  -- TODO
