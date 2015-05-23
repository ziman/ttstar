module Erasure.Prune where

import TT
import Pretty

import Erasure.Meta
import Erasure.Check
import Erasure.Solve

import Util.PrettyPrint

import qualified Data.Set as S

data Annotation = E Relevance | Null deriving Show

instance PrettyR Annotation where
    prettyCol (E r) = prettyCol r
    prettyCol Null  = text ":N:"

    prettyApp (E r) = prettyApp r
    prettyApp Null  = text " "

annotate :: Uses -> Program Meta -> Program Annotation
annotate uses = fmap rel
  where
    rel m@(MVar i 0)
        | m `S.member` uses = E R
        | otherwise         = E I
    rel m@(MVar i tag)
        | m        `S.member` uses = E R
        | MVar i 0 `S.member` uses = Null
        | otherwise                = E I
    rel m@(Fixed R) = E R
    rel m@(Fixed I) = E I

prune :: Program Annotation -> Program ()
prune (Prog defs) = Prog $ concatMap pruneDef defs

pruneDef :: Def Annotation -> [Def ()]
pruneDef (Def n (E I) ty dt) = []
pruneDef (Def n (E R) ty dt) = [Def n () Erased (pruneDefType dt)]

pruneDefType :: DefType Annotation -> DefType ()
pruneDefType  Axiom = Axiom
pruneDefType (Fun tm) = Fun $ pruneTm tm

pruneTm :: TT Annotation -> TT ()
pruneTm (V n) = V n
pruneTm (Bind bnd n (E I) ty tm) = pruneTm tm
pruneTm (Bind bnd n (E R) ty tm) = Bind bnd n () Erased (pruneTm tm)
pruneTm (App (E I) f x) = pruneTm f
pruneTm (App (E R) f x) = App () (pruneTm f) (pruneTm x)
pruneTm (App Null  f x) = App () (pruneTm f) Erased
pruneTm (Case s alts) = Case (pruneTm s) (map pruneAlt alts)
pruneTm Erased = Erased
pruneTm Type = Type

pruneAlt :: Alt Annotation -> Alt ()
pruneAlt (DefaultCase tm) = DefaultCase $ pruneTm tm
pruneAlt (ConCase cn r tm) = ConCase cn () $ pruneTm tm
