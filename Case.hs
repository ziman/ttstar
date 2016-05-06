module Case
    ( compile
    , Def (..)
    )
    where

import qualified TT
import TT (Name, TT, Clause)

data Def r = Def [Name] (Tree r)
data Tree r = Term (TT r) | Case Name [Alt r]
data AltType = Ctor Name [Name] | Wildcard
data Alt r = Alt AltType (Tree r)

compile :: [Clause r] -> Def r
compile = undefined
