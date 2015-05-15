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
