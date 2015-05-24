module Erasure.Prune where

import TT
import Pretty

import Erasure.Meta
import Erasure.Check
import Erasure.Solve

import Util.PrettyPrint

import Control.Applicative
import qualified Data.Set as S

annotate :: Uses -> Program Meta cs -> Program Relevance Void
annotate uses (Prog defs) = Prog $ map (annDef uses) defs

annDef :: Uses -> Def Meta cs -> Def Relevance Void
annDef uses (Def n r ty mtm mcs) = Def n (rel r) (rel <$> ty) (fmap rel <$> mtm) Nothing
  where
    rel m
        | m `S.member` uses = R
        | otherwise         = I

prune :: Program Relevance Void -> Program () Void
prune (Prog defs) = Prog $ concatMap pruneDef defs

pruneDef :: Def Relevance Void -> [Def () Void]
pruneDef (Def n I ty dt mcs) = []
pruneDef (Def n R ty dt mcs) = [Def n () Erased (pruneTm <$> dt) Nothing]

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (Bind bnd n I ty tm) = pruneTm tm
pruneTm (Bind bnd n R ty tm) = Bind bnd n () Erased (pruneTm tm)
pruneTm (App I I f x) = pruneTm f
pruneTm (App R R f x) = App () () (pruneTm f) (pruneTm x)
pruneTm (App R I f x) = App () () (pruneTm f) Erased
pruneTm (App I R f x) = error "relevant application of irrelevant pi"  -- should never happen
pruneTm (Case s alts) = Case (pruneTm s) (map pruneAlt alts)
pruneTm Erased = Erased
pruneTm Type = Type

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (DefaultCase tm) = DefaultCase $ pruneTm tm
pruneAlt (ConCase cn tm) = ConCase cn $ pruneTm tm
