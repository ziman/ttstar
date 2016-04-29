module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT
import TTLens
import Erasure.Check
import Erasure.Meta
import Erasure.Solve

import qualified Data.Set as S
import Lens.Family2

data VerError
    = TCFailure TCFailure
    | InconsistentAnnotation
    deriving Show

verify :: Program Relevance VoidConstrs -> Either VerError ()
verify prog =
    case check (prog & progRelevance %~ Fixed) of
        Left tcfail -> Left (TCFailure tcfail)
        Right (ctx, cs) ->
            let (uses, residue) = solve cs
              in
                if Fixed E `S.member` uses
                  then Left InconsistentAnnotation
                  else Right ()
