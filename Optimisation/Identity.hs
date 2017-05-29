module Optimisation.Identity (optimise) where

import TT

optimise :: TT () -> TT ()
optimise = id
