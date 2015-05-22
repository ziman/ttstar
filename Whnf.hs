module Whnf (whnf) where

import TT
import qualified Data.Map as M

whnf :: TT r -> TT r
whnf tm = tm
