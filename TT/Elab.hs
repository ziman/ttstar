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
    | NoProgress (S.Set Constr)
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

elab :: Term -> Either String Term
elab = runExcept . withExcept show . elab'

-- solve all metas
elab' :: Term -> Except ElabFailure Term
elab' tm = do
    (_ty, cs) <- evalRWST (elabTm tm) (ctx, BT []) (ES 1)
    ms <- solve M.empty cs
    return $ substMeta ms tm
  where
    ctx = M.singleton typeOfTypes
        $ Def typeOfTypes Nothing (V typeOfTypes) (Abstract Constructor)

substMeta :: M.Map Int Term -> Term -> Term
substMeta ms tm@(V n) = tm
substMeta ms m@(Meta i) = case M.lookup i ms of
    Just tm -> tm
    Nothing -> error $ "no solution for meta " ++ show m
substMeta ms (EI n ty) = EI n (substMeta ms ty)
substMeta ms (App r f x) = App r (substMeta ms f) (substMeta ms x)
substMeta ms (Bind bnd ds rhs) =
    Bind bnd (map (substMetaDef ms) ds) (substMeta ms rhs)
  where
    substMetaDef :: M.Map Int Term -> Def MRel -> Def MRel
    substMetaDef ms (Def n r ty b) = Def n r (substMeta ms ty) (substMetaBody ms b)

    substMetaBody :: M.Map Int Term -> Body MRel -> Body MRel
    substMetaBody ms b@(Abstract _) = b
    substMetaBody ms (Term tm) = Term $ substMeta ms tm
    substMetaBody ms (Clauses cs) = Clauses $ map (substMetaClause ms) cs

    substMetaClause :: M.Map Int Term -> Clause MRel -> Clause MRel
    substMetaClause ms (Clause pvs lhs rhs) =
        Clause
            (map (substMetaDef ms) pvs)
            (substMetaPat ms lhs)
            (substMeta ms rhs)

    substMetaPat :: M.Map Int Term -> Pat MRel -> Pat MRel
    substMetaPat ms p@(PV _) = p
    substMetaPat ms (PApp r f x) = PApp r (substMetaPat ms f) (substMetaPat ms x)
    substMetaPat ms (PForced tm) = PForced $ substMeta ms tm
    substMetaPat ms p@(PHead _) = p

solve :: M.Map Int Term -> S.Set Constr -> Except ElabFailure (M.Map Int Term)
solve ms cs
    | S.null cs = return ms
    | cs' == cs = throwE . ElabFailure (BT []) $ NoProgress cs
    | otherwise = solve (M.union ms ms') cs'
  where
    (ms', cs') = solveMany (S.toList cs)

solveMany :: [Constr] -> (M.Map Int Term, S.Set Constr)
solveMany [] = (M.empty, S.empty)
solveMany (c:cs) = case solveOne c of
    Left (i, tm) ->
        let (ms', cs') = solveMany (map (subst i tm) cs)
        in (M.insert i tm ms', cs')

    Right csc ->
        let (ms', cs') = solveMany cs
        in (ms', S.union csc cs')
  where
    subst :: Int -> Term -> Constr -> Constr
    subst i tm (Eq bt lhs rhs) =
        let s = substMeta (M.singleton i tm)
        in Eq bt (s lhs) (s rhs)

solveOne :: Constr -> Either (Int, Term) (S.Set Constr)
solveOne (Eq _ (Meta i) tm) = Left (i,tm)
solveOne (Eq _ tm (Meta i)) = Left (i,tm)
solveOne (Eq _ tm tm') | tm == tm' = Right S.empty
solveOne c = Right [c]
