module Erasure.Annotate where

import TT.Core
import TT.Lens
import Erasure.Evar

import Lens.Family
import qualified Data.Set as S

annotate :: Uses Evar -> Program Evar -> Program Relevance
annotate uses prog = prog & ttRelevance %~ rel
  where
    rel (Fixed r) = r
    rel m
        | m `S.member` uses = R
        | otherwise         = E
