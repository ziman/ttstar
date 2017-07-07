{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}

module Erasure.Infer (infer, instantiate, unions, TCFailure) where

import TT.Core
import TT.Lens
import TT.Utils
import TT.Normalise
import Erasure.Evar
import Erasure.Solve

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
    | NotPi Type
    | InconsistentErasure Name
    | NotImplemented String
    | NonPatvar Name
    | InvalidPattern (Pat Evar)
    | UncheckableTerm TTevar
    | PatvarsPatternMismatch [Name] [Name]
    | NonlinearPattern (Clause Evar)
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

type TCTraceback = [String]
type TCState = Int
type TC a = ReaderT (TCTraceback, Ctx Evar) (ExceptT TCFailure (State TCState)) a

type Term = TT Evar
type Type = TT Evar

infixl 2 /\
(/\) :: Constrs Evar -> Constrs Evar -> Constrs Evar
(/\) = union

infix 3 -->
(-->) :: Evar -> Evar -> Constrs Evar
g --> u = M.singleton (S.singleton g) (S.singleton u)

infix 3 <-->
(<-->) :: Evar -> Evar -> Constrs Evar
p <--> q = p --> q /\ q --> p

union :: Constrs Evar -> Constrs Evar -> Constrs Evar
union = M.unionWith S.union

unions :: [Constrs Evar] -> Constrs Evar
unions = M.unionsWith S.union

cond :: Evar -> Constrs Evar -> Constrs Evar
cond r = M.mapKeysWith S.union (S.insert r)

with :: Def Evar -> TC a -> TC a
with d = with' $ M.insert (defName d) d

withs :: [Def Evar] -> TC a -> TC a
withs []     = id
withs (d:ds) = with d . withs ds

with' :: (Ctx Evar -> Ctx Evar) -> TC a -> TC a
with' f = local $ \(tb, ctx) -> (tb, f ctx)

bt :: Show a => a -> TC b -> TC b
bt dbg sub = do
    ctx <- getCtx
    let btLine = "In context:\n" ++ showCtx ctx ++ "\n" ++ show dbg ++ "\n"
    local (\(tb,ctx) -> (btLine:tb,ctx)) sub

showCtx :: Ctx Evar -> String
showCtx ctx = unlines
    [ "  " ++ show (defName d) ++ " : " ++ show (defType d)
    | d <- M.elems ctx
    ]

tcfail :: TCError -> TC a
tcfail e = do
    (tb, ctx) <- ask
    lift . throwE $ TCFailure e tb

getCtx :: TC (Ctx Evar)
getCtx = do
    (tb, ctx) <- ask
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

runTC :: Int -> Ctx Evar -> TC a -> Either TCFailure a
runTC maxTag ctx tc = evalState (runExceptT $ runReaderT tc ([], ctx)) maxTag

infer :: Program Evar -> Either TCFailure (Constrs Evar)
infer prog = runTC maxTag ctx $ do
    (_ty, cs) <- inferTm prog
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
    let d'' = d'{ defConstraints = reduce $ defConstraints d' }
    with d'' $ inferDefs ds

inferDefs' :: [Def Evar] -> TC [Def Evar]
inferDefs' [] = return []
inferDefs' (d:ds) = do
    d' <- with d{ defBody = Abstract Var } $ inferDef d
    let d'' = d'{ defConstraints = reduce $ defConstraints d' }
    (d'' :) <$> (with d'' $ inferDefs' ds)

inferDef :: Def Evar -> TC (Def Evar)
-- In types, only conversion constraints matter but they *do* matter.
-- We should probably explain on an example why.
--
-- The point is that the conversion infer binds the type signature (the asserted type)
-- with the inferred type, also binding the evarvars in them, so that the signature
-- can later represent the whole definition.

inferDef (Def n r ty (Abstract a) _noCs) = do
    (tyty, tycs) <- inferTm ty
    tytyTypeCs <- conv tyty (V $ UN "Type")
    let cs = tytyTypeCs  -- in types, only conversion constraints matter
    return $ Def n r ty (Abstract a) cs

inferDef d@(Def n r ty (Term tm) _noCs) = bt ("DEF-TERM", n) $ do
    (tmty, tmcs) <- with d $ inferTm tm  -- "with d" because it could be recursive
    (tyty, tycs) <- inferTm ty
    tytyTypeCs   <- conv tyty (V $ UN "Type")
    tyTmtyCs     <- conv ty tmty
    let cs = tmcs /\ tytyTypeCs /\ tyTmtyCs  -- in types, only conversion constraints matter
    return $ Def n r ty (Term tm) cs

inferDef d@(Def n r ty (Clauses cls) _noCs) = bt ("DEF-CLAUSES", n) $ do
    (tyty, tycs) <- inferTm ty
    tytyTypeCs   <- conv tyty (V $ UN "Type")
    cfCs <- with d{ defBody = Abstract Var } $ do
        unions <$> traverse (inferClause ty) cls
    let cs = tytyTypeCs /\ cfCs  -- in types, only conversion constraints matter
    return $ Def n r ty (Clauses cls) cs

inferClause :: Type -> Clause Evar -> TC (Constrs Evar)
inferClause fty c@(Clause pvs lhs rhs) = bt ("CLAUSE", lhs) $ do
    -- check patvars
    ctx <- getCtx
    let pvsN = S.fromList (map defName pvs)
    patN <- case S.unions <$> traverse (freePatVars . snd) lhs of
        Just pvs -> return pvs
        Nothing  -> tcfail $ NonlinearPattern c

    if pvsN /= patN
        then tcfail $ PatvarsPatternMismatch (S.toList pvsN) (S.toList patN)
        else return ()

    pvs' <- inferDefs' pvs
    let pvsCtx = M.fromList [(defName d, d) | d <- pvs']
    (lty, lcs) <- inferPatApp pvsCtx (Fixed R) noConstrs fty lhs
    withs pvs' $ do
        (rty, rcs) <- inferTm rhs
        ccs <- conv lty rty
        return $ lcs /\ rcs /\ ccs

-- the relevance evar "s" stands for "surrounding"
-- it's the relevance of the whole pattern
inferPat :: Ctx Evar -> Evar -> Pat Evar -> TC (Type, Constrs Evar)
inferPat pvs s pat@(PV n) = bt ("PAT-NAME", n) $ do
    case M.lookup n pvs of
        Nothing -> tcfail $ UnknownName n
        Just (Def n r ty (Abstract Var) cs) ->
            return (ty, r --> s)  -- relevance of var forces surrounding to be relevant

        _ -> tcfail $ NonPatvar n

inferPat pvs s pat@(PForced tm) = bt ("PAT-FORCED", tm) $ do
    (ty, cs) <- with' (M.union pvs) $ inferTm tm
    return (ty, cond s cs)

inferPat pvs s pat@(PCtor forced cn args) = bt ("PAT-CTOR", pat) $ do
    d <- lookup cn
    case defBody d of
        Abstract Constructor -> return ()
        _ -> tcfail $ NotConstructor cn

    -- if we inspect, that affects 1) surrounding, 2) ctor relevance
    let ctorCs
          | forced    = noConstrs
          | otherwise = Fixed R --> s /\ Fixed R --> defR d

    inferPatApp pvs s ctorCs (defType d) args

--inferPat s pat@(PApp app_r f x) = bt ("PAT-APP", pat) $ do
inferPatApp :: Ctx Evar -> Evar -> Constrs Evar
    -> Type -> [(Evar, Pat Evar)] -> TC (Type, Constrs Evar)
inferPatApp pvs s cs fty [] = return (fty, cs)
inferPatApp pvs s cs fty ((app_r,x):xs) = bt ("PAT-APP", fty, x) $ do
    (xty, xcs) <- inferPat pvs app_r x  -- it's not (s /\ app_r) -- app_r is absolute
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi [Def n' pi_r ty' (Abstract Var) _noCs] retTy -> do
            tycs <- with' (M.union pvs) $ conv xty ty'
            let cs' =
                    cs
                    /\ cond s (app_r <--> pi_r) -- if we inspect here, then the pi must reflect that
                                                -- but only in relevant surroundings
                                                -- (look at treered_A.tt what happens if you don't cond)
                    /\ app_r --> s    -- if we inspect anywhere here, then the whole pattern inspects
                    /\ xcs
                    /\ cond app_r tycs
                    -- we can't leave tycs out entirely because
                    -- if it's relevant, it needs to be erasure-correct as well
                    -- but if it's not used, then it needn't be erasure-correct
            inferPatApp pvs s cs' (subst n' (pat2term x) retTy) xs

        _ -> do
            tcfail $ NotPi fty

inferTm :: Term -> TC (Type, Constrs Evar)

inferTm t@(V Blank) = tcfail $ UncheckableTerm t

inferTm t@(V n) = bt ("VAR", n) $ do
    -- at the point of usage of a bound name,
    -- the constraints associated with that name come in
    d <- lookup n
    return (defType d, defConstraints d /\ Fixed R --> defR d)

inferTm t@(I n ty) = bt ("INST", n, ty) $ do
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
    return (ty, defConstraints d /\ Fixed R --> defR d /\ convCs)

inferTm t@(Bind Lam [d@(Def n r ty (Abstract Var) _noCs)] tm) = bt ("LAM", t) $ do
    d' <- inferDef d
    (tmty, tmcs) <- with d' $ inferTm tm
    return (Bind Pi [d'] tmty, tmcs)

inferTm t@(Bind Pi [d@(Def n r ty (Abstract Var) _noCs)] tm) = bt ("PI", t) $ do
    d' <- inferDef d
    -- (tyty, _tycs) <- inferTm ty
    -- cs' <- conv (V $ UN "Type") tyty
    tmcs <- with d' $ do
        (tmty, tmcs) <- inferTm tm
        cs <- conv (V $ UN "Type") tmty
        return $ tmcs /\ cs
    return (V $ UN "Type", tmcs)

inferTm t@(Bind Let ds tm) = bt ("LET", t) $ do
    ds' <- inferDefs ds
    (tmty, tmcs) <- with' (M.union ds') $ inferTm tm
    return (tmty, tmcs)

inferTm t@(App app_r f x) = bt ("APP", t) $ do
    (fty, fcs) <- inferTm f
    (xty, xcs) <- inferTm x
    ctx <- getCtx
    case whnf ctx fty of
        Bind Pi [Def n' pi_r ty' (Abstract Var) _noCs] retTy -> do
            tycs <- conv xty ty'
            let cs =
                    -- we can't leave tycs out entirely because
                    -- if it's relevant, it needs to be erasure-correct as well
                    -- but if it's not used, then it needn't be erasure-correct
                    cond pi_r tycs
                    /\ fcs
                    /\ cond pi_r xcs
                    /\ pi_r <--> app_r
            return (subst n' x retTy, cs)

        _ -> do
            tcfail $ NonFunction f fty

inferTm tm = bt ("UNCHECKABLE-TERM", tm) $ do
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
        xs <- conv ty ty' -- (rename n' n ty')
        ys <- with (Def n r ty (Abstract Var) noConstrs)
                $ conv tm (rename n' n tm')
        return $ xs /\ ys /\ r <--> r'

{- This would be necessary for conversion-checking of multilets. Let's disable them for now.
conv' (Bind b (d:ds) tm) (Bind b' (d':ds') tm') = bt ("C-SIMPL", b) $
    conv' (Bind b [d] $ Bind b ds tm) (Bind b' [d'] $ Bind b' ds' tm')
-}

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    xs <- conv f f'
    ys <- conv x x'
    return $ xs /\ ys /\ r <--> r'

-- we don't include a case for Forced because those constructors
-- get normalised away to bare terms

conv' p q = tcfail $ CantConvert p q
