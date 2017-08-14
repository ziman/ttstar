module Codegen.IR where

data IName
    = IUN String
    deriving (Eq, Ord, Show)

data IR
    = IV IName
    | ILam IName IR
    | ILet IName IBody IR
    | IApp IR IR
    | IError String
    deriving (Eq, Ord, Show)

data IBody
    = ICaseFun [Int] ICaseTree
    | IConstructor Int
    | IForeign String
    deriving (Eq, Ord, Show)

data ICaseTree
    = ICase Int [IAlt]
    | ILeaf IR
    deriving (Eq, Ord, Show)

data IAlt
    = ICtor IName [Int] ICaseTree
    | IDefault ICaseTree
    deriving (Eq, Ord, Show)
