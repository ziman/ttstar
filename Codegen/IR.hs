module Codegen.IR where

data IName
    = IMN String Int  -- number-disambiguated name
    | IPV Int         -- pattern variable
    deriving (Eq, Ord, Show)

data IR
    = IV IName
    | ILam IName IR
    | ILet IName IBody IR
    | IApp IR IR
    | IError String
    deriving (Eq, Ord, Show)

data IBody
    = ICaseTree ICaseTree
    | IConstructor Int
    | IForeign String
    deriving (Eq, Ord, Show)

data ICaseTree
    = ICase IName [IAlt]
    | ILeaf IR
    deriving (Eq, Ord, Show)

data IAlt
    = ICtor IName [IName] ICaseTree
    | IDefault ICaseTree
    deriving (Eq, Ord, Show)
