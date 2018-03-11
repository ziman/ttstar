module Solver.Indexed (solve, reduce) where

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

-- reduce the constraint set, keeping the empty-guard constraint
-- we could use the simple solver for smaller sets
-- but benchmarks show that there's almost no runtime difference
reduce :: Impls Evar -> Impls Evar
reduce cs
    | S.null (S.delete (Fixed R) us) = residue
    | otherwise = M.insert S.empty us residue
  where
    (us, residue) = solve cs

type Constraint = (Guards Evar, Uses Evar)
type Constraints = IntMap Constraint
type Index = Map Evar IntSet

-- it turns out that this cleaning makes stuff slower
toNumbered :: Impls Evar -> Constraints
toNumbered = IM.fromList . zip [0..] {- . filter informative .  map clean -} . M.toList
{-
  where
    informative (gs, us) = (not $ S.null us)  -- && (Fixed E `S.notMember` gs)
    clean (gs, us) = (gs, S.delete (Fixed R) us {- S.\\ gs -})
-}

fromNumbered :: Constraints -> Impls Evar
fromNumbered = IM.foldr addConstraint M.empty
  where
    addConstraint (ns, vs) = M.insertWith S.union ns vs

solve :: Impls Evar -> (Uses Evar, Impls Evar)
solve cs
    = second fromNumbered
    $ step (index csN) initialUses initialUses csN
  where
    csN = toNumbered cs

    initialUses :: Uses Evar
    initialUses = S.insert (Fixed R) $ M.findWithDefault S.empty S.empty cs

    index :: Constraints -> Index
    index = IM.foldrWithKey (
            -- for each clause (i. ns --> _ds)
            \i (ns, _ds) ix -> foldr (
                -- for each node `n` in `ns`
                \n ix' -> M.insertWith IS.union n (IS.singleton i) ix'
              ) ix (S.toList ns)
        ) M.empty

    step :: Index -> Uses Evar -> Uses Evar -> Constraints -> (Uses Evar, Constraints)
    step index previouslyNew ans cs
        | S.null currentlyNew = (ans, prunedCs)
        | otherwise = step index currentlyNew (S.union ans currentlyNew) prunedCs
      where
        affectedIxs = IS.unions [
            M.findWithDefault IS.empty n index
            | n <- S.toList previouslyNew
          ]

        (currentlyNew, prunedCs)
            = IS.foldr
                (reduceConstraint previouslyNew)
                (S.empty, cs)
                affectedIxs

        -- Update the pair (newly reached nodes, numbered constraint set)
        -- by reducing the constraint with the given number.
        reduceConstraint
            :: Set Evar  -- ^ nodes reached in the previous iteration
            -> Int       -- ^ constraint number
            -> (Uses Evar, Constraints)
            -> (Uses Evar, Constraints)
        reduceConstraint previouslyNew i (news, constrs)
            | Just (cond, deps) <- IM.lookup i constrs
            = case cond S.\\ previouslyNew of
                cond'
                    -- This constraint's set of preconditions has shrunk
                    -- to the empty set. We can add its RHS to the set of newly
                    -- reached nodes, and remove the constraint altogether.
                    | S.null cond'
                    -> (S.union news deps, IM.delete i constrs)

                    -- This constraint's set of preconditions has shrunk
                    -- so we need to overwrite the numbered slot
                    -- with the updated constraint.
                    | S.size cond' < S.size cond
                    -> (news, IM.insert i (cond', deps) constrs)

                    -- This constraint's set of preconditions hasn't changed
                    -- so we do not do anything about it.
                    | otherwise
                    -> (news, constrs)

            -- Constraint number present in index but not found
            -- among the constraints. This happens more and more frequently
            -- as we delete constraints from the set.
            | otherwise = (news, constrs)

