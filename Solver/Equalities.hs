{-# LANGUAGE RankNTypes #-}
module Solver.Equalities
    ( mergeEvars
    , replaceEvars
    ) where

import TT.Core
import Erasure.Evar

import Data.Functor.Identity
import Lens.Family2.Unchecked

import qualified Data.Map as M
import qualified Data.Set as S

data Merge = Merge
    { mCls :: M.Map Evar (S.Set Evar)  -- representant -> represented evars
    , mIdx :: M.Map Evar Evar          -- represented -> representant
    }

-- a = f Evar
-- b = f Evar
-- but because `f` might be a type synonym, Haskell won't let us say so
replaceEvars
    :: M.Map Evar Evar
    -> Traversal a b Evar Evar
    -> a
    -> b
replaceEvars evarMap traversal
    = runIdentity . traversal (\r -> return $ M.findWithDefault r r evarMap)

mergeEvars :: Eqs Evar -> M.Map Evar Evar
mergeEvars = mIdx . foldr mergeEvar mrgInitial . S.toList

-- start with R and E being representants
-- so that they are always chosen as representants
mrgInitial :: Merge
mrgInitial = Merge
    { mCls = M.fromList
        [ (Fixed E, S.singleton $ Fixed E)
        , (Fixed R, S.singleton $ Fixed R)
        ]
    , mIdx = M.fromList
        [ (Fixed E, Fixed E)
        , (Fixed R, Fixed R)
        ]
    }

mergeEvar :: (Evar, Evar) -> Merge -> Merge
mergeEvar (r, s) (Merge cls idx) = case (M.lookup r idx, M.lookup s idx) of
    (Nothing, Nothing) -> Merge
        { mCls = M.insert r (S.fromList [r,s]) cls
        , mIdx = idx `M.union` M.fromList
            [(r, r), (s, r)]
        }

    (Nothing, Just sCls) -> Merge
        { mCls = M.insertWith S.union sCls (S.singleton r) cls
        , mIdx = M.insert r sCls idx
        }

    (Just rCls, Nothing) -> Merge
        { mCls = M.insertWith S.union rCls (S.singleton s) cls
        , mIdx = M.insert s rCls idx
        }

    (Just rCls, Just sCls)
        | rEvars <- cls M.! rCls
        , sEvars <- cls M.! sCls
        -> if rCls /= Fixed R && rCls /= Fixed E && S.size rEvars <= S.size sEvars
            -- if rEvars is smaller, merge it into sEvars
            then Merge
                { mCls
                    = M.insertWith S.union sCls rEvars
                    . M.delete rCls
                    $ cls
                , mIdx = foldr (\r ix -> M.insert r sCls ix) idx (S.toList rEvars)
                }
            -- otherwise merge sEvars into rEvars
            else Merge
                { mCls
                    = M.insertWith S.union rCls sEvars
                    . M.delete sCls
                    $ cls
                , mIdx = foldr (\s ix -> M.insert s rCls ix) idx (S.toList sEvars)
                }
