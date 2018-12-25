{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}

module Erasure.Infer (infer, instantiate, unions, TCFailure) where

import TT.Core
import TT.Lens
import TT.Utils
import TT.Normalise
import Erasure.Evar

import Prelude hiding (lookup)

import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader

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
type TC a = ReaderT (ConstrRedFun, TCTraceback, Ctx Evar) (ExceptT TCFailure (State TCState)) a

type Term = TT Evar
type Type = TT Evar

infixl 2 /\
(/\) :: Constrs Evar -> Constrs Evar -> Constrs Evar
Constrs impls /\ Constrs impls' = Constrs $ M.unionWith S.union impls impls'

infix 3 -->
(-->) :: Guards Evar -> Uses Evar -> Constrs Evar
ps --> qs = Constrs $ M.singleton guards uses

infix 3 <->
(<->) :: S.Set Evar -> S.Set Evar -> Constrs Evar
ps <-> qs = p --> q /\ q --> p

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

constrRedFun :: TC ConstrRedFun
constrRedFun = do
    (redConstrs, tb, ctx) <- ask
    return redConstrs

runTC :: ConstrRedFun -> Int -> Ctx Evar -> TC a -> Either TCFailure a
runTC redConstrs maxTag ctx tc = evalState (runExceptT $ runReaderT tc (redConstrs, [], ctx)) maxTag

infer :: ConstrRedFun -> Program Evar -> Either TCFailure (Constrs Evar)
infer redConstrs prog = runTC redConstrs maxTag ctx $ do
    (_ty, cs) <- inferTm [Fixed R] prog
    return cs
  where
    getTag :: Evar -> Int
    getTag (EV i) = i
    getTag _        = 0  -- whatever, we're looking for maximum

    allTags :: [Int]
    allTags = map getTag (prog ^.. (ttRelevance :: Traversal' (Program Evar) Evar))

    maxTag = L.maximum allTags

    ctx = builtins (Fixed relOfType)

inferDefs :: [Def Evar] -> TC (Ctx Evar)
inferDefs [] = getCtx
inferDefs (d:ds) = do
    d' <- with d{ defBody = Abstract Var } $ inferDef d
    redConstrs <- constrRedFun
    let d'' = d'{ defConstraints = redConstrs $ defConstraints d' }
    with d'' $ inferDefs ds

inferDefs' :: [Def Evar] -> TC [Def Evar]
inferDefs' [] = return []
inferDefs' (d:ds) = do
    d' <- with d{ defBody = Abstract Var } $ inferDef d
    redConstrs <- constrRedFun
    let d'' = d'{ defConstraints = redConstrs $ defConstraints d' }
    (d'' :) <$> (with d'' $ inferDefs' ds)

inferDef :: Def Evar -> TC (Def Evar)
-- In types, only conversion constraints matter but they *do* matter.
-- We should probably explain on an example why.
--
-- The point is that the conversion infer binds the type signature (the asserted type)
-- with the inferred type, also binding the evars in them, so that the signature
-- can later represent the whole definition.

inferDef (Def n r ty (Abstract a) _noCs) = do
    -- check type
    (tyty, tycs) <- inferTm [Fixed E] ty
    tytyTypeCs <- conv tyty (V $ UN "Type")

    -- no constraints because the type is always erased
    return $ Def n r ty (Abstract a) noConstrs

inferDef d@(Def n r ty (Term tm) _noCs) = bt ("DEF-TERM", n) $ do
    -- check type
    (tyty, tycs) <- inferTm [Fixed E] ty
    _ <- conv tyty (V $ UN "Type")

    -- check body
    (tmty, tmcs) <- with d $ inferTm [r] tm  -- "with d" because it could be recursive
    tmTyCs       <- conv ty tmty

    return $ Def n r ty (Term tm) (tmcs /\ tmTyCs)

inferDef d@(Def n r ty (Clauses cls) _noCs) = bt ("DEF-CLAUSES", n) $ do
    -- check type
    (tyty, tycs) <- inferTm [Fixed E] ty
    _ <- conv tyty (V $ UN "Type")

    -- check clauses
    clauseCs <- with d{ defBody = Abstract Var } $ do
        unions <$> traverse (inferClause r) cls

    return $ Def n r ty (Clauses cls) clauseCs

inferClause :: Evar -> Clause Evar -> TC (Constrs Evar)
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
    pvs' <- inferDefs' pvs
    let pvs'Ctx = M.fromList [(defName d, d) | d <- pvs']

    -- check LHS vs. RHS
    (lty, lcs) <- inferPat q q pvs'Ctx lhs
    withs pvs' $ do
        (rty, rcs) <- inferTm [q] rhs
        ccs <- conv lty rty
        return $ lcs /\ rcs /\ ccs

-- the relevance evar "s" stands for "surrounding"
-- it's the relevance of the whole pattern
inferPat
    :: Evar
    -> Guards Evar
    -> Ctx Evar
    -> Pat Evar
    -> TC (Type, Constrs Evar)
inferPat q s pvs pat@(PV n)
    | Just d <- M.lookup n pvs
    = bt ("PAT-VAR", n) $ do
        return (defType d, [defR d] <-> s)

-- this must be a constructor if it's not a patvar
inferPat q s pvs pat@(PV n) = bt ("PAT-REF", n) $ do
    d@(Def n r ty body cs) <- lookup n
    case body of
        Abstract Constructor           -- here we inspect: that affects 1) surrounding, 2) ctor relevance
            -> return (
                    ty,
                    [q] --> s /\ [q] --> [r]
                )
        _
            -> tcfail $ InvalidPattern pat

inferPat q s pvs pat@(PForced tm) = bt ("PAT-FORCED", tm) $
    with' (M.union pvs) $ inferTm s tm

inferPat q s pvs pat@(PApp appR f x) = bt ("PAT-APP", pat) $ do
    (fty, fcs) <- inferPat q s pvs f
    (xty, xcs) <- inferPat q (s <> [appR]) pvs x
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi [Def n' piR ty' (Abstract Var) _noCs] retTy -> do
            xtycs <- with' (M.union pvs) $ conv xty ty'
            let cs =
                    -- [appR] --> s  -- if something inspects, the whole thing inspects (not necessary?)
                    [piR] <-> [appR] -- the two must match
                    /\ fcs
                    /\ xcs
                    /\ xtycs

            return (subst n' (pat2term x) retTy, cs)

        _ -> do
            tcfail $ NonFunction (pat2term f) fty

inferPat q s pvs pat@(PHead f) = bt ("PAT-HEAD", pat) $ do
    d <- lookup f
    case defBody d of
        Abstract Var -> return (defType d, [q] <-> s /\ [defR] <-> s)
        _ -> tcfail $ NotPatternHead f

inferTm
    :: Guards Evar
    -> Term
    -> TC (Type, Constrs Evar)

inferTm s t@(V Blank) = tcfail $ UncheckableTerm t

inferTm s t@(V n) = bt ("VAR", n) $ do
    -- at the point of usage of a bound name,
    -- the constraints associated with that name come in
    d <- lookup n
    return (defType d, s --> [defR d])

inferTm s t@(EI n ty) = bt ("INST", n, ty) $ do
    -- here, we need to freshen the constraints before bringing them up
    d <- instantiate freshTag IM.empty =<< lookup n
    convCs <- conv (defType d) ty
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
    return (ty, [] --> [defR d] /\ convCs)

inferTm s t@(Bind Lam [d@(Def n r ty (Abstract Var) _noCs)] tm) = bt ("LAM", t) $ do
    d' <- inferDef d
    (tmty, tmcs) <- with d' $ inferTm s tm
    return (Bind Pi [d'] tmty, tmcs)

inferTm s t@(Bind Pi [d@(Def n r ty (Abstract Var) _noCs)] tm) = bt ("PI", t) $ do
    d' <- inferDef d
    -- (tyty, _tycs) <- inferTm ty
    -- cs' <- conv (V $ UN "Type") tyty
    tmcs <- with d' $ do
        (tmty, tmcs) <- inferTm s tm
        cs <- conv (V $ UN "Type") tmty
        return $ tmcs /\ cs
    return (V $ UN "Type", tmcs)

inferTm s t@(Bind Let ds tm) = bt ("LET", t) $ do
    ds' <- inferDefs ds
    (tmty, tmcs) <- with' (M.union ds') $ inferTm tm
    return (tmty, tmcs /\ union [defCs d | d <- ds'])

inferTm s t@(App appR f x) = bt ("APP", t) $ do
    (fty, fcs) <- inferTm s f
    (xty, xcs) <- inferTm (s <> [appR]) x
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi [Def n' piR ty' (Abstract Var) _noCs] retTy -> do
            xtycs <- conv xty ty'
            let cs =
                    fcs
                    /\ xcs
                    /\ xtycs
                    /\ [piR] <-> [appR]
            return (subst n' x retTy, cs)

        _ -> do
            tcfail $ NonFunction f fty

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
-- this function does not take the relevance variable of the context
-- because in inference, we always assume we're relevant.
-- Because this can be overriden using "cond", anyway.
conv :: Type -> Type -> TC (Constrs Evar)
conv p q = do
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
        tycs <- conv ty ty' -- (rename n' n ty')
        tmcs <- with (Def n r ty (Abstract Var) noConstrs)
                $ conv tm (rename n' n tm')
        return $ tycs /\ tmcs /\ r <-> r'

{- This would be necessary for conversion-checking of multilets. Let's disable them for now.
conv' (Bind b (d:ds) tm) (Bind b' (d':ds') tm') = bt ("C-SIMPL", b) $
    conv' (Bind b [d] $ Bind b ds tm) (Bind b' [d'] $ Bind b' ds' tm')
-}

-- special case for irrelevant applications
conv' p@(App (Fixed I) f x) q@(App (Fixed I) f' x') = bt ("C-APP", p, q) $ do
    conv f f'
    -- TODO: we could probably infer irrelevance of one side from the other

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    fcs <- conv f f'
    xcs <- conv x x'
    return $ fcs /\ xcs /\ r <-> r'

-- we don't include a case for Forced because those constructors
-- get normalised away to bare terms

conv' p q = tcfail $ CantConvert p q
