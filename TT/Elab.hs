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
    | NotPi Type
    | NotConstructor Name
    | BadPatHead Name
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

withs :: [Def MRel] -> Elab a -> Elab a
withs [] x = x
withs (d:ds) x = with d $ withs ds x

elabDefs :: [Def MRel] -> Elab ()
elabDefs [] = pure ()
elabDefs (d:ds) = do
    elabDef d
    with d $ elabDefs ds

elabDef :: Def MRel -> Elab ()
elabDef d@(Def n _r ty b) = do
    tyty <- elabTm ty
    tyty ~= V typeOfTypes
    with d{ defBody = Abstract Var } $ elabBody n b

elabBody :: Name -> Body MRel -> Elab ()
elabBody _ (Abstract _) = pure ()
elabBody n (Term tm) = do
    ty  <- defType <$> lookup n
    ty' <- elabTm tm
    ty' ~= ty
elabBody n (Clauses cs) = mapM_ (elabClause n) cs

elabClause :: Name -> Clause MRel -> Elab ()
elabClause n (Clause pvs lhs rhs) = do
    elabDefs pvs
    lty <- elabPat n (M.fromList [(defName d, d) | d <- pvs]) lhs
    rty <- withs pvs $ elabTm rhs   
    lty ~= rty

elabPat :: Name -> Ctx MRel -> Pat MRel -> Elab Type
elabPat n pvs (PV n') = case M.lookup n' pvs of
    Just d -> return $ defType d
    Nothing -> do
        d <- lookup n'
        case defBody d of
            Abstract Constructor -> return $ defType d
            _ -> efail $ NotConstructor n'

elabPat n pvs (PApp r f x) = do
    fty <- elabPat n pvs f
    xty <- elabPat n pvs x
    ctx <- fst <$> ask

    case nf (pvs `M.union` ctx) fty of
        Bind Pi [Def n' r' ty' (Abstract Var)] rhs' -> do
            xty ~= ty'
            return $ subst n' (ptt x) rhs'

        fty' -> efail $ NotPi fty' 

elabPat n pvs (PForced tm) = withs (M.elems pvs) $ elabTm tm

elabPat n pvs (PHead n')
    | n == n' = defType <$> lookup n
    | otherwise = efail $ BadPatHead n'

ptt :: Pat MRel -> Term
ptt (PV n) = V n
ptt (PApp r f x) = App r (ptt f) (ptt x)
ptt (PForced tm) = tm
ptt (PHead n) = V n

elabBnd :: Def MRel -> Type -> Binder -> Elab Type
elabBnd d rty Lam = return $ Bind Pi [d] rty
elabBnd d rty Pi  = do
    rty ~= V typeOfTypes
    return $ V typeOfTypes
elabBnd _d rty Let = return rty

elabTm :: Term -> Elab Type

elabTm (V n) = do
    d <- lookup n
    return $ defType d

elabTm (Meta i) = freshMeta

elabTm (EI _n ty) = do
    tyty <- elabTm ty
    tyty ~= V typeOfTypes

    return ty

elabTm (Bind bnd [d] rhs) = do
    elabDef d
    rty <- with d $ elabTm rhs
    elabBnd d rty bnd 

elabTm (Bind Let (d:ds) rhs) =
    elabTm $ Bind Let [d] (Bind Let ds rhs)

elabTm (App r f x) = do
    fty <- elabTm f
    xty <- elabTm x
    ctx <- fst <$> ask

    case nf ctx fty of
        Bind Pi [Def n r ty (Abstract Var)] rhs -> do
            xty ~= ty
            return $ subst n x rhs

        fty' -> efail $ NotPi fty'

elabTm tm = efail $ CantElaborate tm

-- solve all metas
elab :: Term -> Either String Term
elab tm =
    case runExcept $ evalRWST (elabTm tm) (ctx, BT []) (ES 1) of
        Left err -> Left $ show err
        Right (_ty, cs) -> error $ show cs
  where
    ctx = M.singleton typeOfTypes $ Def typeOfTypes Nothing (V typeOfTypes) (Abstract Constructor)
