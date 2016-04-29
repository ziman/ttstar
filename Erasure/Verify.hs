module Erasure.Verify (verify) where

import TT

verify :: Program Relevance VoidConstrs -> Either String ()
verify prog = Right ()
