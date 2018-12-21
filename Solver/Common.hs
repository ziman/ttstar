module Solver.Common
    ( mergeEvars
    ) where

import TT.Core

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

data Merge = Merge
    { mCls :: IM.IntMap (S.Set Evar)
    , mIdx :: M.Map Evar Int
    }

mergeEvars :: Eqs Evar -> M.Map Evar Evar
mergeEvars = mrgResult . foldr mergeEvar mrgInitial . S.toList

mrgResult :: Merge Evar -> M.Map Evar Evar
mrgResult (Merge _cls idx) = M.map EV idx

mrgInitial :: Merge
mrgInitial = Merge IM.empty M.empty

mergeEvar :: (Evar, Evar) -> Merge -> Merge
mergeEvar (r, s) (Merge cls idx) = case (M.lookup r idx, M.lookup s idx) of
    (Nothing, Nothing) -> let freshClsNr = IM.size cls in Merge
        { mCls = M.insert freshClsNr (S.fromList [r,s]) cls
        , mIdx = idx `M.union` M.fromList
            [(r, freshClsNr), (s, freshClsNr)]
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
    | rEvars <- cls IM.! rCls
    | sEvars <- cls IM.! sCls
    -> if S.size rEvars <= S.size sEvars
        -- if rEvars is smaller, merge it into sEvars
        then Merge
            { mCls
                = IM.insertWith S.union sCls rEvars
                . IM.delete rCls
                $ cls
            , mIdx = foldr (\r ix -> IM.insert r sCls ix) idx (S.toList rCls)
            }
        -- otherwise merge sEvars into rEvars
        then Merge
            { mCls
                = IM.insertWith S.union rCls sEvars
                . IM.delete sCls
                $ cls
            , mIdx = foldr (\s ix -> IM.insert s rCls ix) idx (S.toList sCls)
            }
