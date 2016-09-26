module Codegen.Common (Codegen(..)) where

import TT
import Util.PrettyPrint

data Codegen = Codegen
    { cgRun :: Program () -> Doc
    , cgExt :: String
    }
