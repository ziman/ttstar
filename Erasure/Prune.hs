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
        | otherwise         = E

prune :: Program Relevance Void -> Program () Void
prune (Prog defs) = Prog $ concatMap pruneDef defs

pruneDef :: Def Relevance Void -> [Def () Void]
pruneDef (Def n E ty dt mcs) = []
pruneDef (Def n R ty dt mcs) = [Def n () Erased (pruneTm <$> dt) Nothing]

pruneTm :: TT Relevance -> TT ()
pruneTm (V n) = V n
pruneTm (Bind bnd n E ty E tm) = pruneTm tm  -- never used
pruneTm (Bind bnd n E ty R tm) = Bind bnd n () Erased () (pruneTm tm)  -- used somewhere polymorphically
pruneTm (Bind bnd n R ty _ tm) = Bind bnd n () Erased () (pruneTm tm)
pruneTm (App E E f x) = pruneTm f
pruneTm (App E R f x) = App () () (pruneTm f) Erased
pruneTm (App R R f x) = App () () (pruneTm f) (pruneTm x)
pruneTm (App R E f x) = error "irrelevant application of relevant pi"  -- should never happen
pruneTm (Let (Def n E ty mtm Nothing) tm) = pruneTm tm
pruneTm (Let (Def n R ty mtm Nothing) tm) = Let (Def n () Erased (pruneTm <$> mtm) Nothing) (pruneTm tm)
pruneTm (Case s alts) = Case (pruneTm s) (map pruneAlt alts)
pruneTm Erased = Erased
pruneTm Type = Type

pruneAlt :: Alt Relevance -> Alt ()
pruneAlt (DefaultCase tm) = DefaultCase $ pruneTm tm
pruneAlt (ConCase cn tm) = ConCase cn $ pruneTm tm
