module TT.Constrs (CTrie) where

import E

import qualified Data.IntSet as IS
import qualified Data.IntMap as IM

data CTrie = CT IS.IntSet (IM.IntMap CTrie) | CInconsistent deriving (Eq, Ord, Show)

ctSingleton :: Evar
