module Solver.LMS (solve, reduce) where

-- The "Last Man Standing" solver.
-- Adapted from "Chaff: Engineering an efficient SAT solver"
-- by Moskewicz et al., 2001.

import TT.Core
import Erasure.Evar

import Control.Arrow

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

import Data.IntSet (IntSet)
import qualified Data.IntSet as IS

reduce :: Constrs Evar -> Constrs Evar
reduce (Constrs impls) = Constrs (reduceImpls impls)

-- reduce the constraint set, keeping the empty-guard constraint
-- we could use the simple solver for smaller sets
-- but benchmarks show that there's almost no runtime difference
reduceImpls :: Impls Evar -> Impls Evar
reduceImpls impls
    | S.null (S.delete (Fixed R) us) = residue
    | otherwise = M.insert S.empty us residue
  where
    (us, residue) = solve impls

type Constraint = (Guards Evar, Uses Evar)
type Constraints = IntMap Constraint
data Index = Index
    { _ixSelected    :: Map Evar IntSet
    , _ixFrequencies :: Map Evar Int
    }

toNumbered :: Impls Evar -> Constraints
toNumbered = IM.fromList . zip [0..] . M.toList

fromNumbered :: Constraints -> Impls Evar
fromNumbered = IM.foldr addConstraint M.empty
  where
    addConstraint (ns, vs) = M.insertWith S.union ns vs

-- choosing just the first one seems to be faster than choosing the least frequent
rarestEvar :: Map Evar Int -> Set Evar -> Evar
rarestEvar frequencies = head . S.toList -- minimumBy (comparing frequency) . S.toList
  where
    _frequency n = M.findWithDefault 0 n frequencies

solve :: Impls Evar -> (Uses Evar, Impls Evar)
solve cs
    = second fromNumbered
    $ step index initialUses initialUses csN
  where
    csN = toNumbered cs
    index = Index selected frequencies

    initialUses :: Uses Evar
    initialUses = S.insert (Fixed R) $ M.findWithDefault S.empty S.empty cs

    frequencies :: Map Evar Int
    frequencies
        = foldr (\n -> M.insertWith (+) n 1) M.empty
            $ concat [S.toList us | (_,(gs, us)) <- IM.toList csN]

    selected :: Map Evar IntSet
    selected = IM.foldrWithKey select M.empty csN
      where
        select i (gs, _us)
            | S.null gs = id  -- don't select anything from empty bodies
            | otherwise = M.insertWith IS.union (rarestEvar frequencies gs) (IS.singleton i)

    step :: Index -> Uses Evar -> Uses Evar -> Constraints -> (Uses Evar, Constraints)
    step (Index selected frequencies) previouslyNew ans cs
        | S.null currentlyNew = (ans, prunedCs)
        | otherwise = step (Index selected' frequencies) currentlyNew (S.union ans currentlyNew) prunedCs
      where
        affectedIxs = IS.unions [
            M.findWithDefault IS.empty n selected
            | n <- S.toList previouslyNew
          ]

        (currentlyNew, prunedCs, selected')
            = IS.foldr
                (reduceConstraint ans)
                (S.empty, cs, selected)
                affectedIxs

        -- Update the pair (newly reached nodes, numbered constraint set)
        -- by reducing the constraint with the given number.
        reduceConstraint
            :: Set Evar  -- ^ nodes reached up to and including the previous iteration
            -> Int       -- ^ constraint number
            -> (Uses Evar, Constraints, Map Evar IntSet)
            -> (Uses Evar, Constraints, Map Evar IntSet)
        reduceConstraint ans i (news, constrs, selected)
            | Just (cond, deps) <- IM.lookup i constrs
            = case cond S.\\ ans of
                cond'
                    -- This constraint's set of preconditions has shrunk
                    -- to the empty set. We can add its RHS to the set of newly
                    -- reached nodes, and remove the constraint altogether.
                    | S.null cond'
                    -> (S.union news deps, IM.delete i constrs, selected)

                    -- This constraint's set of preconditions has shrunk
                    -- so we need to overwrite the numbered slot
                    -- with the updated constraint.
                    --
                    -- We also need to pick the rarest evar from the new set.
                    | S.size cond' < S.size cond
                    -> let e = rarestEvar frequencies cond'
                        in ( news
                           , IM.insert i (cond', deps) constrs
                           , M.insertWith IS.union e (IS.singleton i) selected
                           )

                    -- This constraint's set of preconditions hasn't changed
                    -- so we do not do anything about it.
                    | otherwise
                    -> (news, constrs, selected)

            -- Constraint number present in index but not found
            -- among the constraints. This happens more and more frequently
            -- as we delete constraints from the set.
            | otherwise = (news, constrs, selected)

