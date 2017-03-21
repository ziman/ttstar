{-# LANGUAGE RankNTypes #-}

module Codegen.Common (Codegen(..)) where

import TT
import Util.PrettyPrint

data Codegen = Codegen
    { cgRun :: forall r. Program r -> Doc
    , cgExt :: String
    }
