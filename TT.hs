{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module TT where

import Control.Applicative
import qualified Data.Map as M

data Name = UN String | IN String [Relevance] | Blank deriving (Eq, Ord)
data Relevance = E | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi | Let deriving (Eq, Ord, Show)

instance Show Name where
    show Blank  = "_"
    show (UN n) = n
    show (IN n rs) = n ++ "_" ++ concatMap show rs

newtype Void = Void Void deriving (Eq, Ord, Show)
type VoidConstrs = Const Void

voidElim :: Void -> a
voidElim (Void v) = voidElim v

data TT r
    = V Name
    | I Name (TT r)  -- instance of a global definition with a specific erasure type
    | Bind Binder (Def r VoidConstrs) (TT r)
    | App r (TT r) (TT r)
    | Forced (TT r)  -- forced terms don't generate constraints
    deriving (Eq, Ord)

data CaseFun r = CaseFun
    { cfArgs :: [Def r VoidConstrs]
    , cfTree :: CaseTree r
    } deriving (Eq, Ord)

data CaseTree r
    = Leaf (TT r)
    | Case (TT r) [Alt r]
    deriving (Eq, Ord)

data AltLHS r
    = Ctor Name [Def r VoidConstrs] [(Name, TT r)]
    | Wildcard
    deriving (Eq, Ord)

data Alt r = Alt
    { altLHS :: AltLHS r
    , altRHS :: CaseTree r
    } deriving (Eq, Ord)

-- The difference between Var and Postulate is that for Var, the value is unknown,
-- for postulate; the term itself is the value. A variable stands for something else,
-- a postulate stands for itself.
data Abstractness = Var | Postulate deriving (Eq, Ord, Show)
data Body r = Abstract Abstractness | Term (TT r) | Patterns (CaseFun r) deriving (Eq, Ord)
data Def r cs = Def
    { defName :: Name
    , defR    :: r
    , defType :: TT r
    , defBody :: Body r
    , defConstraints :: Maybe (cs r)
    } deriving (Eq, Ord)

type Ctx r cs = M.Map Name (Def r cs)

newtype Program r cs = Prog { getDefs :: [Def r cs] } deriving (Eq, Ord)

builtins :: r -> Ctx r cs
builtins r = M.fromList
    [ (UN "Type", Def (UN "Type") r (V $ UN "Type") (Abstract Postulate) Nothing)
    ]
