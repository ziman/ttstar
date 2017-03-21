{-# LANGUAGE RankNTypes #-}

module Codegen.Common (Codegen(..)) where

import TT
import Pretty
import Util.PrettyPrint

data Codegen = Codegen
    { cgRun :: forall r. PrettyR r => Program r -> Doc
    , cgExt :: String
    }
