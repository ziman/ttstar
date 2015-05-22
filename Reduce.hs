module Reduce where

import TT
import qualified Data.Map as M

type Ctx r cs = M.Map Name (r, TT r, Maybe (TT r), cs)

