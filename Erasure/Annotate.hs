module Erasure.Annotate where

import TT
import TTLens
import Erasure.Meta
import Erasure.Solve

import Lens.Family
import Control.Applicative
import qualified Data.Set as S

annotate :: Uses -> Program Meta cs -> Program Relevance VoidConstrs
annotate uses (Prog defs) = Prog $ map (annDef uses) defs

annDef :: Uses -> Def Meta cs -> Def Relevance VoidConstrs
annDef uses (Def n r ty body mcs)
    = Def n (rel r)
        (ty & ttRelevance %~ rel)
        (body & bodyRelevance %~ rel)
        Nothing
  where
    rel (Fixed r) = r
    rel m
        | m `S.member` uses = R
        | otherwise         = E
