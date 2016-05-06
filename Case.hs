module Case
    ( compile
    , CaseDef (..)
    )
    where

import TT

data CaseDef r = CaseDef [Name] (Tree r)
data Tree r = Term (TT r) | Case Name [Alt r]
data AltType = Ctor Name [Name] | Wildcard
data Alt r = Alt AltType (Tree r)

compile :: [Clause r] -> CaseDef r
compile = undefined
