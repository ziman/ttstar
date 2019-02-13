{-# LANGUAGE OverloadedLists #-}
module TT.Elab (elab) where

import TT.Core
import TT.Pretty ()
import TT.Normalise
import TT.Utils

import Prelude hiding (lookup)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.RWS.Strict

import qualified Data.Set as S
import qualified Data.Map as M

type MRel = Maybe Relevance
type Term = TT MRel
type Type = TT MRel

data ElabState = ES Int
data ElabErr
    = CantUnify Term Term
    | CantElaborate Term
    | UnknownVar Name
    | NotPi Term Type
    deriving (Show)

newtype Backtrace = BT [String]
data Constr = Eq Backtrace Term Term

instance Eq Constr where
    Eq _ p q == Eq _ p' q' = (p == p') && (q == q')

instance Ord Constr where
    compare (Eq _ p q) (Eq _ p' q') = compare p p' <> compare q q'

instance Show Constr where
    show (Eq _ p q) = "(" ++ show p ++ " ~ " ++ show q ++ ")"

data ElabFailure = ElabFailure Backtrace ElabErr
instance Show ElabFailure where
    show (ElabFailure (BT []) e) = show e
    show (ElabFailure (BT bt) e) = unlines $
            "Traceback:"
            : zipWith
                (\i n -> show i ++ ". " ++ n)
                [1::Integer ..]
                (reverse bt)
            ++ ["Error: " ++ show e]


type Elab a = RWST
    (Ctx MRel, Backtrace) -- R: context
    (S.Set Constr)        -- W: constraints
    ElabState             -- S: for fresh names
    (Except ElabFailure)  -- T: errors
    a

efail :: ElabErr -> Elab a
efail err = do
    (_, bt) <- ask
    lift . throwE $ ElabFailure bt err

lookup :: Name -> Elab (Def MRel)
lookup n = do
    (ctx, _) <- ask
    case M.lookup n ctx of
        Just d -> return d
        Nothing -> efail $ UnknownVar n

freshMeta :: Elab Term
freshMeta = do
    ES j <- get
    put $ ES (j+1)
    return $ Meta j

(~=) :: Term -> Term -> Elab ()
p ~= q = do
    (_, bt) <- ask
    tell [Eq bt p q]

with :: Def MRel -> Elab a -> Elab a
with d = local $ \(ctx, bt) -> (M.insert (defName d) d ctx, bt)

elabTm :: Term -> Elab Type
elabTm (V n) = do
    d <- lookup n
    return $ defType d

elabTm (Meta i) = freshMeta

elabTm (EI _n ty) = do
    tyty <- elabTm ty
    tyty ~= V typeOfTypes

    return ty

elabTm (Bind Lam [d@(Def n r ty (Abstract Var))] rhs) = do
    tyty <- elabTm ty
    tyty ~= V typeOfTypes
    rty <- with d $ elabTm rhs
    return $ Bind Pi [d] rty

elabTm (Bind Pi [d@(Def n r ty (Abstract Var))] rhs) = do
    tyty <- elabTm ty
    tyty ~= V typeOfTypes

    rty <- with d $ elabTm rhs
    rty ~= V typeOfTypes

    return $ V typeOfTypes

elabTm (Bind Let [d] rhs) = with d $ elabTm rhs

elabTm (Bind Let (d:ds) rhs) = with d $ elabTm (Bind Let ds rhs)

elabTm (App r f x) = do
    fty <- elabTm f
    xty <- elabTm x
    ctx <- fst <$> ask

    case nf ctx fty of
        Bind Pi [Def n r ty (Abstract Var)] rhs -> do
            xty ~= ty
            return $ subst n x rhs

        fty' -> efail $ NotPi f fty'

elabTm tm = efail $ CantElaborate tm

-- solve all metas
elab :: Term -> Either String Term
elab tm =
    case runExcept $ evalRWST (elabTm tm) (M.empty, BT []) (ES 1) of
        Left err -> Left $ show err
        Right (_ty, cs) -> error $ show cs
