module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT

data VerError
    = RelevanceMismatch Relevance Relevance
    | Other String
    deriving (Eq, Ord, Show)

verify :: Program Relevance VoidConstrs -> Either VerError ()
verify prog = Right ()
