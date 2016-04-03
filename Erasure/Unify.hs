module Erasure.Unify
    ( unify
    , Stuck, Subst
    ) where

import TT
import Erasure.Meta

import Control.Monad.Trans.State

import qualified Data.Set as S
import qualified Data.Map as M

-- Stuck equations
type Problem r = (TT r, TT r)
type Stuck r = S.Set (Problem r)

-- Solved substitution.
type Subst r cs = [(Name, TT r)]

type Unify r a = State (Stuck r) a

unify :: Ord r => Stuck r -> (Subst r cs, Stuck r)
unify = runState $ iterUnif []

iterUnif :: Ord r => Subst r cs -> Unify r (Subst r cs)
iterUnif substSoFar = do
    eqs <- attack
    if null eqs
        -- reverse trickity-trick to keep the ordering
        -- *and* O(|eqs|) complexity
        then return $ reverse substSoFar
        else iterUnif $ reverse eqs ++ substSoFar

attack :: Ord r => Unify r (Subst r cs)
attack = do
    simples <- concat <$> (traverse findSimple . S.toList =<< get)
    -- nothing else beyond simples at the moment
    return simples

discard :: Ord r => Problem r -> Unify r ()
discard p = put . S.delete p =<< get

findSimple :: Ord r => (TT r, TT r) -> Unify r (Subst r cs)
findSimple p@(V n, tm) = discard p *> pure [(n, tm)]
findSimple p@(tm, V n) = discard p *> pure [(n, tm)]
findSimple _ = return []
