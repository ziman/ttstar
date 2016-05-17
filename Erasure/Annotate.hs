module Erasure.Annotate where

import TT
import TTLens
import Erasure.Meta
import Erasure.Solve

import Lens.Family
import Control.Applicative
import qualified Data.Set as S

annotate :: Uses Meta -> Program Meta -> Program Relevance
annotate uses (Prog defs) = Prog $ map (annDef uses) defs

annDef :: Uses Meta -> Def Meta -> Def Relevance
annDef uses (Def n r ty body cs)
    = Def n (rel r)
        (ty & ttRelevance %~ rel)
        (body & bodyRelevance %~ rel)
        noConstrs
  where
    rel (Fixed r) = r
    rel m
        | m `S.member` uses = R
        | otherwise         = E
