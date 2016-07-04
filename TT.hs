module TT where

import qualified Data.Set as S
import qualified Data.Map as M

data Name
    = UN String
    | IN String [Relevance]
    | Blank
    deriving (Eq, Ord)

data Relevance = E | R deriving (Eq, Ord, Show)

data Binder = Lam | Pi | Let deriving (Eq, Ord, Show)

instance Show Name where
    show Blank  = "_"
    show (UN n) = n
    show (IN n rs) = n ++ "_" ++ concatMap show rs

type Guards  r = S.Set r
type Uses    r = S.Set r
type Constrs r = M.Map (Guards r) (Uses r)

data TT r
    = V Name
    | I Name (TT r)  -- instance of a global definition with a specific erasure type
    | Bind Binder (Def r) (TT r)
    | Case r (TT r) (TT r) [Alt r]  -- r, scrut, type, alts
    | App r (TT r) (TT r)
    deriving (Eq, Ord)

type Subst r = [(Name, TT r)]

data AltLHS r
    = Ctor Name [Def r] (Subst r)
    | Wildcard
    deriving (Eq, Ord)

data Alt r = Alt
    { altLHS :: AltLHS r
    , altRHS :: TT r
    } deriving (Eq, Ord)

-- The difference between Var and Postulate is that for Var, the value is unknown,
-- for postulate; the term itself is the value. A variable stands for something else,
-- a postulate stands for itself.
data Abstractness = Var | Postulate deriving (Eq, Ord, Show)
data Body r = Abstract Abstractness | Term (TT r) deriving (Eq, Ord)
data Def r = Def
    { defName :: Name
    , defR    :: r
    , defType :: TT r
    , defBody :: Body r
    , defConstraints :: Constrs r
    } deriving (Eq, Ord)

type Ctx r = M.Map Name (Def r)

newtype Program r = Prog { getDefs :: [Def r] } deriving (Eq, Ord)

noConstrs :: Constrs r
noConstrs = M.empty

builtins :: r -> Ctx r
builtins r = M.fromList
    [ (UN "Type", Def (UN "Type") r (V $ UN "Type") (Abstract Postulate) noConstrs)
    ]
