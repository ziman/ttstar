module Erasure.Unify
    ( unify
    , Stuck, Subst
    ) where

import TT
import Erasure.Meta

import qualified Data.Map as M

-- Stuck equations
type Stuck r = [(TT r, TT r)]

-- Solved substitution.
type Subst = Ctx

unify :: [(TT r, TT r)] -> (Subst r cs, Stuck r)
unify eqs = (M.empty, eqs)
