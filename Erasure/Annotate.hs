module Erasure.Annotate where

import TT
import TTLens
import Erasure.Meta

import Lens.Family
import qualified Data.Set as S

annotate :: Uses Meta -> Program Meta -> Program Relevance
annotate uses prog = prog & ttRelevance %~ rel
  where
    rel (Fixed r) = r
    rel m
        | m `S.member` uses = R
        | otherwise         = E
