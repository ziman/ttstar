module IR.Core where

data IName
    = IUN String
    | IBlank
    deriving (Eq, Ord)

data IR
    = IV IName
    | ILam IName IR
    | ILet IName IBody IR
    | IApp IR IR
    | IError String
    deriving (Eq, Ord)

data IBody
    = ICaseFun [Int] ICaseTree
    | IConstructor Int
    | IForeign String
    deriving (Eq, Ord)

data ICaseTree
    = ICase Int [IAlt]
    | ILeaf IR
    deriving (Eq, Ord)

data IAlt
    = ICtor IName [Int] ICaseTree
    | IDefault ICaseTree
    deriving (Eq, Ord)
