{-# LANGUAGE FlexibleInstances #-}
module TTstar where

import Data.List

type Name = String
data Relevance = I | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi deriving (Eq, Ord, Show)

data TT' r
    = V Name
    | Bind Binder r Name (TT' r) (TT' r)
    | App r (TT' r) (TT' r)
    | Case (TT' r) [Alt r]  -- scrutinee, scrutinee type, alts
    | Type
    | Erased
    deriving (Eq, Ord)

data Alt r
    = ConCase Name r [Name] (TT' r)  -- relevance of tag + relevance of args
    | DefaultCase (TT' r)
    deriving (Eq, Ord, Show)

data DefType r = Axiom | Fun (TT' r) deriving (Eq, Ord, Show)
data Def r = Def r Name (TT' r) (DefType r) deriving (Eq, Ord, Show)

newtype Program r = Prog [Def r]

type TT = TT' (Maybe Relevance)
type TTstar = TT' Relevance
type MRel = Maybe Relevance

instance Functor TT' where
    fmap _ (V n) = V n
    fmap f (Bind b r n ty tm) = Bind b (f r) n (fmap f ty) (fmap f tm)
    fmap f (App r fun arg) = App (f r) (fmap f fun) (fmap f arg)
    fmap f (Case s alts) = Case (fmap f s) (map (fmap f) alts)
    fmap _ Erased = Erased
    fmap _ Type = Type

instance Functor Alt where
    fmap f (ConCase cn r ns tm) = ConCase cn (f r) ns (fmap f tm)
    fmap f (DefaultCase tm) = DefaultCase (fmap f tm)

instance Functor DefType where
    fmap _  Axiom = Axiom
    fmap f (Fun tm) = Fun (fmap f tm)

instance Functor Def where
    fmap f (Def r n ty dt) = Def (f r) n (fmap f ty) (fmap f dt)

instance Functor Program where
    fmap f (Prog defs) = Prog (map (fmap f) defs)

class Show r => ShowR r where
    showR :: r -> String
    showX :: r -> String

instance ShowR Relevance where
    showR x = ":" ++ show x ++ ":"
    showX x = " -" ++ show x ++ "- "

instance ShowR () where
    showR _ = ":"
    showX _ = " "

instance ShowR (Maybe Relevance) where
    showR Nothing = ":"
    showR (Just r) = showR r

    showX Nothing = " "
    showX (Just r) = showX r

instance ShowR r => Show (Program r) where
    show (Prog defs) = intercalate "\n" $ map fmtDef defs
      where
        fmtDef (Def _r n Erased dt) = n ++ " = " ++ fmtDT dt ++ "\n"
        fmtDef (Def r n ty dt) = intercalate "\n"
            [ n ++ " " ++ showR r ++ " " ++ show ty
            , n ++ " = " ++ fmtDT dt
            , ""
            ]

        fmtDT Axiom = "(axiom)"
        fmtDT (Fun tm) = show tm

instance ShowR r => Show (TT' r) where
    show (V n) = n
    show (Bind Pi r n ty tm) = "(" ++ n ++ showR r ++ show ty ++ ") -> " ++ show tm
    show (Bind Lam _r n Erased tm) = "\\" ++ n ++ ". " ++ show tm
    show (Bind Lam r n ty tm) = "\\" ++ n ++ showR r ++ show ty ++ ". " ++ show tm
    show (App r f x) = "(" ++ show' r f x ++ ")"
      where
        show' r (App r' f' x') x = show' r' f' x' ++ showX r ++ show x
        show' r f x = show f ++ showX r ++ show x
    show (Case s alts) = "case " ++ show s ++ " of " ++ show alts
    show Erased = "____"
    show Type = "*"
