module Solver.Graph (solve) where

import TT.Core
import Erasure.Evar

import Data.Map (Map)
import qualified Data.Map as M

import qualified Data.Set as S

import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

import Data.IntSet (IntSet)
import qualified Data.IntSet as IS

import Control.Monad.Trans.State

data Vertex = Vertex
    { nThreshold :: Int
    , nFlowIn    :: Int
    , nEdgesOut  :: IntSet
    , nEvar      :: Maybe Evar
    }
    deriving (Eq, Ord, Show)

type Graph = IntMap Vertex
type EvarIndex = Map Evar Int

addVertex :: Vertex -> Graph -> (Int, Graph)
addVertex v g = (vertexNo, IM.insert vertexNo v g)
  where
    vertexNo = IM.size g

solve :: Impls Evar -> Uses Evar
solve cs' = evalState (increments initialVertices) graph
  where
    cs = M.insertWith S.union S.empty (S.singleton $ Fixed R) cs'

    allEvars = S.union (S.unions $ M.keys cs) (S.unions $ M.elems cs)
    (terminals, evarIndex) = S.foldr addTerminal (IM.empty, M.empty) allEvars
    graph = M.foldrWithKey (addConstraint evarIndex) terminals cs
    initialEvars = M.findWithDefault S.empty S.empty cs
    initialVertices = IS.fromList [evarIndex M.! e | e <- S.toList initialEvars]

addTerminal :: Evar -> (Graph, EvarIndex) -> (Graph, EvarIndex)
addTerminal e (g, ix) = (g', M.insert e i ix)
  where
    vertex = Vertex 1 0 IS.empty (Just e)
    (i, g') = addVertex vertex g

addConstraint :: Map Evar Int -> Guards Evar -> Uses Evar -> Graph -> Graph
addConstraint ix gs us g = S.foldr (addEdgeIn i ix) g' gs
  where
    vertex = Vertex (S.size gs) 0 edgesOut Nothing
    edgesOut = IS.fromList [ix M.! e | e <- S.toList us]
    (i, g') = addVertex vertex g

addEdgeIn :: Int -> Map Evar Int -> Evar -> Graph -> Graph
addEdgeIn i ix e = IM.adjust (\v -> v{ nEdgesOut = IS.insert i $ nEdgesOut v }) j
  where
    j = ix M.! e

type GM a = State Graph a

getVertex :: Int -> GM Vertex
getVertex i = (IM.! i) <$> get

putVertex :: Int -> Vertex -> GM ()
putVertex i v = modify $ IM.insert i v 

increment :: Int -> GM (S.Set Evar)
increment i = do
    -- increment the vertex
    v' <- getVertex i
    let v = v'{ nFlowIn = nFlowIn v' + 1 }
    putVertex i v

    -- propagate the change
    if nFlowIn v /= nThreshold v
        then return S.empty
        else do
            evs <- increments $ nEdgesOut v
            return $ case nEvar v of
                Nothing -> evs
                Just e  -> S.insert e evs

increments :: IntSet -> GM (S.Set Evar)
increments is = S.unions <$> traverse increment (IS.toList is)
