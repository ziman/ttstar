module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT
import TTLens
import Erasure.Check
import Erasure.Meta
import Erasure.Solve

import qualified Data.Map as M
import qualified Data.Set as S
import Lens.Family2

data VerError
    = TCFailure TCFailure
    | InconsistentAnnotation
    deriving Show

-- TODO: make this a separate/independent typechecker
-- rather than reusing the possibly buggy typechecker-elaborator?

verify :: Program Relevance -> Either VerError ()
verify prog =
    case check (prog & progRelevance %~ Fixed) of
        Left tcfail -> Left (TCFailure tcfail)
        Right ctx ->
            let (uses, residue) = solve . defConstraints $ ctx M.! (UN "main")
              in
                if Fixed E `S.member` uses
                  then Left InconsistentAnnotation
                  else Right ()
