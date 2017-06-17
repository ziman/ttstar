module TT.Core where

import qualified Data.Set as S
import qualified Data.Map as M

data Name
    = UN String
    | IN String [Relevance]
    | MN String Int
    | Blank
    deriving (Eq, Ord)

data Relevance = E | R deriving (Eq, Ord, Show)

data Binder = Lam | Pi | Let deriving (Eq, Ord, Show)

instance Show Name where
    show Blank  = "_"
    show (UN n) = n
    show (IN n rs) = n ++ "_" ++ concatMap show rs
    show (MN n i) = '_' : n ++ show i

type Guards  r = S.Set r
type Uses    r = S.Set r
type Constrs r = M.Map (Guards r) (Uses r)

data TT r
    = V Name
    | I Name (TT r)  -- instance of a global definition with a specific erasure type
    | Bind Binder [Def r] (TT r)
    | App r (TT r) (TT r)
    deriving (Eq, Ord)

data Pat r
    = PV Name
    | PApp r (Pat r) (Pat r)
    | PForced (TT r)
    | PForcedCtor Name
    deriving (Eq, Ord)

data Clause r = Clause
    { cPatVars :: [Def r]
    , cLHS :: Pat r
    , cRHS :: TT r
    } deriving (Eq, Ord)

-- The difference between Var and Postulate is that for Var, the value is unknown,
-- for postulate; the term itself is the value. A variable stands for something else,
-- a postulate stands for itself.
data Abstractness = Var | Postulate | Foreign String deriving (Eq, Ord, Show)
data Body r = Abstract Abstractness | Term (TT r) | Clauses [Clause r] deriving (Eq, Ord)
data Def r = Def
    { defName :: Name
    , defR    :: r
    , defType :: TT r
    , defBody :: Body r
    , defConstraints :: Constrs r
    } deriving (Eq, Ord)

type Ctx r = M.Map Name (Def r)

-- a program is just a term
-- (usually a big let-expression)
type Program r = TT r

noConstrs :: Constrs r
noConstrs = M.empty

typeOfTypes :: Name
typeOfTypes = UN "Type"

builtins :: r -> Ctx r
builtins r = M.fromList
    [ (typeOfTypes, Def typeOfTypes r (V typeOfTypes) (Abstract Postulate) noConstrs)
    ]

relOfType :: Relevance
relOfType = R
