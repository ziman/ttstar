module Erasure.Annotate where

import TT
import TTLens
import Lens.Family
import qualified Data.Set as S

import Erasure.Solve

annotate :: Uses -> Program Meta cs -> Program Relevance VoidConstrs
annotate uses (Prog defs) = Prog $ map (annDef uses) defs

annDef :: Uses -> Def Meta cs -> Def Relevance VoidConstrs
annDef uses (Def n r ty mtm mcs)
    = Def n (rel r) (annTm ty) (annTm <$> mtm) Nothing
  where
    annTm tm = tm & ttRelevance %~ rel
    rel m
        | m `S.member` uses = R
        | otherwise         = E
