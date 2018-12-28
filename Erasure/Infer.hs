{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}

module Erasure.Infer (infer, instantiate, unions, TCFailure) where

import TT.Core
import TT.Lens
import TT.Utils
import TT.Normalise
import Erasure.Evar

import Prelude hiding (lookup)

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.RWS.Strict

import Lens.Family2

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

--import Debug.Trace

data TCError
    = CantConvert TTevar TTevar
    | Mismatch String String
    | UnknownName Name
    | WrongType TTevar TTevar  -- term, type
    | BadCtorType TTevar
    | NonFunction TTevar TTevar  -- term, type
    | EmptyCaseTree TTevar
    | CantMatch TTevar TTevar
    | NonVariableScrutinee TTevar
    | NotConstructor Name
    | NotPatternHead Name
    | InconsistentErasure Name
    | NotImplemented String
    | NonPatvar Name
    | InvalidPattern (Pat Evar)
    | UncheckableTerm TTevar
    | PatvarsPatternMismatch [Name] [Name]
    | NonlinearPattern (Pat Evar)
    | Other String
    deriving (Eq, Ord, Show)

data TCFailure = TCFailure TCError [String]

instance Show TCFailure where
    show (TCFailure e []) = show e
    show (TCFailure e tb) = unlines $
            "Traceback:"
            : zipWith
                (\i n -> show i ++ ". " ++ n)
                [1::Integer ..]
                (reverse tb)
            ++ ["Error: " ++ show e]

type ConstrRedFun = Constrs Evar -> Constrs Evar
type TCTraceback = [String]
type TCState = Int
-- type TC a = ReaderT (ConstrRedFun, TCTraceback, Ctx Evar) (ExceptT TCFailure (State TCState)) a
type TC a = RWST
    (ConstrRedFun, TCTraceback, Ctx Evar)  -- context
    (Constr Evar)                          -- constraints
    TCState                                -- for fresh names
    (ExceptT TCFailure)                    -- errors
    a

type Term = TT Evar
type Type = TT Evar

{-
infixl 2 /\
(/\) :: Constrs Evar -> Constrs Evar -> Constrs Evar
Constrs impls /\ Constrs impls' = Constrs $ M.unionWith S.union impls impls'
-}

infix 3 -->
(-->) :: Guards Evar -> Uses Evar -> TC ()
ps --> qs = tell . Constrs $ M.singleton ps qs

infix 3 <->
(<->) :: S.Set Evar -> S.Set Evar -> TC ()
ps <-> qs = ps --> qs >> qs --> ps

unions :: [Constrs Evar] -> Constrs Evar
unions = foldr (/\) noConstrs

with :: Def Evar -> TC a -> TC a
with d = with' $ M.insert (defName d) d

withs :: [Def Evar] -> TC a -> TC a
withs []     = id
withs (d:ds) = with d . withs ds

with' :: (Ctx Evar -> Ctx Evar) -> TC a -> TC a
with' f = local $ \(rc, tb, ctx) -> (rc, tb, f ctx)

bt :: Show a => a -> TC b -> TC b
bt dbg sub = do
    ctx <- getCtx
    let btLine = "In context:\n" ++ showCtx ctx ++ "\n" ++ show dbg ++ "\n"
    local (\(rc, tb,ctx) -> (rc, btLine:tb,ctx)) sub

showCtx :: Ctx Evar -> String
showCtx ctx = unlines
    [ "  " ++ show (defName d) ++ " : " ++ show (defType d)
    | d <- M.elems ctx
    ]

tcfail :: TCError -> TC a
tcfail e = do
    (redConstrs, tb, ctx) <- ask
    lift . throwE $ TCFailure e tb

getCtx :: TC (Ctx Evar)
getCtx = do
    (redConstrs, tb, ctx) <- ask
    return ctx

require :: Bool -> TCError -> TC ()
require True  e = return ()
require False e = tcfail e

lookup :: Name -> TC (Def Evar)
lookup n = do
    ctx <- getCtx
    case M.lookup n ctx of
        Just x  -> return x
        Nothing -> tcfail $ UnknownName n

freshTag :: TC Int
freshTag = lift $ lift (modify (+1) >> get)

constrSimplifyF :: TC ConstrRedFun
constrSimplifyF = do
    (redConstrs, tb, ctx) <- ask
    return redConstrs

runTC :: ConstrRedFun -> Int -> Ctx Evar -> TC a
    -> Either TCFailure (a, Constrs Evar)
runTC redConstrs maxTag ctx tc
    = runExceptT
    $ evalRWST tc (redConstrs, [], ctx)) maxTag

infer :: ConstrRedFun -> Program Evar -> Either TCFailure (Constrs Evar)
infer redConstrs prog = runTC redConstrs maxTag ctx $ do
    (cs, _ty) <- inferTm [] prog
    return cs
  where
    getTag :: Evar -> Int
    getTag (EV i) = i
    getTag _        = 0  -- whatever, we're looking for maximum

    allTags :: [Int]
    allTags = map getTag (prog ^.. (ttRelevance :: Traversal' (Program Evar) Evar))

    maxTag = L.maximum allTags

    ctx = builtins (Fixed relOfType)

inferDefs :: [Def Evar] -> TC ()
inferDefs [] = pure ()
inferDefs (d:ds) = do
    simplifyF <- constrSimplifyF  -- constraint simplification
    censor simplifyF $ do
        with d{ defBody = Abstract Var } $ inferDef d
        with d $ inferDefs ds

inferDef :: Def Evar -> TC ()
inferDef (Def n r ty (Abstract a)) = do
    -- check type
    tyty <- inferTm [Fixed E] ty
    tyty ~= V typeOfTypes

inferDef d@(Def n r ty (Term tm)) = bt ("DEF-TERM", n) $ do
    -- check type
    tyty <- inferTm [Fixed E] ty
    tyty ~= V typeOfTypes

    -- check body
    tmty <- with d{ defBody = Abstract Var } $ inferTm [r] tm  -- "with d" because it could be recursive
    ty ~= tmty

inferDef d@(Def n r ty (Clauses cls)) = bt ("DEF-CLAUSES", n) $ do
    -- check type
    tyty <- inferTm [Fixed E] ty
    tyty ~= V typeOfTypes

    -- check clauses
    with d{ defBody = Abstract Var }
        $ traverse (inferClause r) cls

inferClause :: Evar -> Clause Evar -> TC ()
inferClause q (Clause pvs lhs rhs) = bt ("CLAUSE", lhs) $ do
    ctx <- getCtx

    -- check patvar names
    let pvsN = S.fromList (map defName pvs)
    patN <- case freePatVars ctx lhs of
        Just pvs -> return pvs
        Nothing  -> tcfail $ NonlinearPattern lhs

    if pvsN /= patN
        then tcfail $ PatvarsPatternMismatch (S.toList pvsN) (S.toList patN)
        else return ()

    -- check patvars
    inferDefs pvs
    let pvsCtx = M.fromList [(defName d, d) | d <- pvs]

    -- check LHS vs. RHS
    lty <- inferPat q [q] pvsCtx lhs
    withs pvs $ do
        rty <- inferTm [q] rhs
        lty ~= rty

inferPat
    :: Evar
    -> Guards Evar
    -> Ctx Evar
    -> Pat Evar
    -> TC (Type, Constrs Evar)
inferPat q gs pvs pat@(PV n)
    | Just (Def n r ty (Abstract Var)) <- M.lookup n pvs
    = bt ("PAT-VAR", n) $ do
        r <-> gs
        return ty

-- this must be a constructor if it's not a patvar
inferPat q gs pvs pat@(PV n) = bt ("PAT-REF", n) $ do
    d@(Def _n r ty body cs) <- lookup n
    case body of
        Abstract Constructor -> do
            [q] --> gs
            [q] --> r
            return ty

        _ -> tcfail $ InvalidPattern pat

inferPat q gs pvs pat@(PForced tm) = bt ("PAT-FORCED", tm) $
    with' (M.union pvs) $ inferTm gs tm

inferPat q gs pvs pat@(PApp appR f x) = bt ("PAT-APP", pat) $ do
    fty <- inferPat q gs pvs f
    xty <- inferPat q (gs <> [appR]) pvs x
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi [Def n' piR ty' (Abstract Var) _noCs] retTy -> do
            with' (M.union pvs)
                $ xty ~= ty'

            [piR] <-> [appR]

            return $ subst n' (pat2term x) retTy

        _ -> tcfail $ NonFunction (pat2term f) fty

inferPat q gs pvs pat@(PHead f) = bt ("PAT-HEAD", pat) $ do
    Def _n r ty body <- lookup f
    case body of
        Abstract Var -> do
            [q] <-> gs
            [r] <-> gs
            return ty

        _ -> tcfail $ NotPatternHead f

inferTm :: Guards Evar -> Term -> TC Type

inferTm gs t@(V Blank) = tcfail $ UncheckableTerm t

inferTm gs t@(V n) = bt ("VAR", n) $ do
    Def _n r ty _body <- lookup n
    gs --> [r]
    return ty

inferTm gs t@(EI n ty) = bt ("INST", n, ty) $ do
    -- check that the type makes sense
    tyty <- inferTm [Fixed E] ty
    tyty ~= V typeOfTypes

    -- create a copy of the definition
    di <- instantiate freshTag IM.empty =<< lookup n

    -- check it
    inferDef di

    -- make the instance compatible with ty
    defType di ~= ty

    -- This (Fixed R --> r) thing is tricky.
    --
    -- We should not include (Fixed R --> r) because it will be an instance
    -- of this function that's runtime-relevant, not the function itself.
    --
    -- However, we must mark the instance as runtime-relevant, but it does not
    -- exist yet. Hence we mark the original function as runtime-relevant as a proxy
    -- for the relevance of the instance, and all instances will inherit this relevance.
    --
    -- In the next iteration of typechecking after specialisation,
    -- the original function will be recognised as erased again, if necessary.
    --
    -- Also, all unused instances should be recognised as erased (I didn't check that).
    
    [] -> [defR d]

    return ty

inferTm gs t@(Bind Lam [d@(Def n r ty (Abstract Var))] tm) = bt ("LAM", t) $ do
    inferDef d
    tmty <- with d $ inferTm gs tm
    return $ Bind Pi [d'] tmty

inferTm gs t@(Bind Pi [d@(Def n r ty (Abstract Var))] tm) = bt ("PI", t) $ do
    inferDef d
    with d' $ do
        tmty <- inferTm gs tm
        tmty ~= V typeOfTypes
    return (V typeOfTypes)

inferTm gs t@(Bind Let ds tm) = bt ("LET", t) $ do
    inferDefs ds
    with' (M.union ds') $ inferTm gs tm

inferTm gs t@(App appR f x) = bt ("APP", t) $ do
    fty <- inferTm gs f
    xty <- inferTm (gs <> [appR]) x
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi [Def n' piR piTy (Abstract Var) _noCs] retTy -> do
            xty ~= piTy
            [piR] <-> [appR]
            return $ subst n' x retTy

        _ -> tcfail $ NonFunction f fty

inferTm gs tm = bt ("UNCHECKABLE-TERM", tm) $ do
    tcfail $ UncheckableTerm tm

freshen :: Monad m => m Int -> Evar -> StateT (IM.IntMap Evar) m Evar
freshen freshTag m@(Fixed r) = return m
freshen freshTag (EV i) = do
    imap <- get
    case IM.lookup i imap of
        Just j ->
            return j
        Nothing -> do
            j <- EV <$> lift freshTag
            modify $ IM.insert i j
            return j

instantiate :: Monad m => m Int -> IM.IntMap Evar -> Def Evar -> m (Def Evar)
instantiate freshTag evarMap def = evalStateT refresh evarMap
  where
    refresh = defRelevance (freshen freshTag) def

-- left: from context (from outside), right: from expression (from inside)
infix 2 ~=
(~=) :: Type -> Type -> TC ()
p ~= q = do
    ctx <- getCtx
    conv' (whnf ctx p) (whnf ctx q)

-- note that this function gets arguments in WHNF
conv' :: Type -> Type -> TC (Constrs Evar)

-- whnf is variable (something irreducible, constructor or axiom)
conv' (V n) (V n') = bt ("C-VAR", n, n') $ do
    require (n == n') $ Mismatch (show n) (show n')
    return noConstrs

conv' p@(Bind b [Def n r ty (Abstract Var) _noCs] tm) q@(Bind b' [Def n' r' ty' (Abstract Var) _noCs'] tm')
    = bt ("C-BIND", p, q) $ do
        require (b == b') $ Mismatch (show b) (show b')
        [r] <-> [r']
        ty ~= ty' -- (rename n' n ty')
        with (Def n r ty (Abstract Var) noConstrs)
                $ tm ~= rename n' n tm'

{- This would be necessary for conversion-checking of multilets. Let's disable them for now.
conv' (Bind b (d:ds) tm) (Bind b' (d':ds') tm') = bt ("C-SIMPL", b) $
    conv' (Bind b [d] $ Bind b ds tm) (Bind b' [d'] $ Bind b' ds' tm')
-}

-- special case for irrelevant applications
conv' p@(App (Fixed I) f x) q@(App (Fixed I) f' x')
    = bt ("C-APP", p, q) $ f ~= f
    -- TODO: we could probably infer irrelevance of one side from the other

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    f ~= f
    x ~= x
    [r] <-> [r']

-- we don't include a case for Forced because those constructors
-- get normalised away to bare terms

conv' p q = tcfail $ CantConvert p q
