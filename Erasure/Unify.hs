module Erasure.Unify
    ( unify
    , Stuck, Subst
    ) where

import TT
import Erasure.Meta

import qualified Data.Set as S
import qualified Data.Map as M

-- Stuck equations
type Stuck r = S.Set (TT r, TT r)

-- Solved substitution.
type Subst r cs = [(Name, TT r)]

unify :: Ord r => Stuck r -> (Subst r cs, Stuck r)
unify eqs = ([], eqs)
