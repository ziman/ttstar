{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving #-}

module Erasure.Check (check, instantiate) where

import TT
import TTLens
import Whnf
import Erasure.Meta
import Erasure.Solve

import Prelude hiding (lookup)

import Data.Maybe
import Data.Foldable
import Control.Monad
import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Except
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader

import Lens.Family

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap as IM

import Debug.Trace

data TCError
    = CantConvert TTmeta TTmeta
    | Mismatch String String
    | UnknownName Name
    | WrongType TTmeta TTmeta  -- term, type
    | BadCtorType TTmeta
    | NonFunction TTmeta TTmeta  -- term, type
    | EmptyCaseTree TTmeta
    | CantMatch TTmeta TTmeta
    | InconsistentErasure Name
    | NotImplemented String
    | Other String
    deriving (Eq, Ord, Show)

data TCFailure = TCFailure TCError [String]

instance Show TCFailure where
    show (TCFailure e []) = show e
    show (TCFailure e tb) = unlines $
        show e : "Traceback:"
            : zipWith
                (\i n -> show i ++ ". " ++ n)
                [1..]
                (reverse tb)

type TCTraceback = [String]
type TCState = Int
type TC a = ReaderT (TCTraceback, Ctx Meta Constrs') (ExceptT TCFailure (State TCState)) a
type Sig = (Meta, Type, Constrs)  -- relevance, type, constraints

type Term = TT Meta
type Type = TT Meta

infixl 2 /\
(/\) :: Constrs -> Constrs -> Constrs
(/\) = union

infix 3 -->
(-->) :: Meta -> Meta -> Constrs
g --> u = CS $ M.singleton (S.singleton g) (S.singleton u)

infix 3 <-->
(<-->) :: Meta -> Meta -> Constrs
p <--> q = p --> q /\ q --> p

eq :: Meta -> Meta -> Constrs
eq p q = p <--> q

union :: Constrs -> Constrs -> Constrs
union (CS x) (CS y) = CS $ M.unionWith S.union x y

unions :: [Constrs] -> Constrs
unions = CS . M.unionsWith S.union . map runCS

noConstrs :: Constrs
noConstrs = CS M.empty

cond :: Meta -> Constrs -> Constrs
cond r = CS . M.mapKeysWith S.union (S.insert r) . runCS

with :: Def Meta Constrs' -> TC a -> TC a
with d@(Def n r ty mtm mcs) = local $ \(tb, ctx) -> (tb, M.insert n d ctx)

bt :: Show a => a -> TC b -> TC b
bt dbg sub = do
    ctx <- getCtx
    let btLine = "In context:\n" ++ showCtx ctx ++ "\n" ++ show dbg ++ "\n"
    local (\(tb,ctx) -> (btLine:tb,ctx)) sub

showCtx :: Ctx Meta Constrs' -> String
showCtx ctx = unlines
    [ "  " ++ show n ++ " : " ++ show ty
    | (n, Def _n _r ty _mtm _mcs) <- M.toList ctx
    ]

tcfail :: TCError -> TC a
tcfail e = do
    (tb, ctx) <- ask
    lift . throwE $ TCFailure e tb

getCtx :: TC (Ctx Meta Constrs')
getCtx = do
    (tb, ctx) <- ask
    return ctx

require :: Bool -> TCError -> TC ()
require True  e = return ()
require False e = tcfail e

lookup :: Name -> TC (Def Meta Constrs')
lookup n = do
    ctx <- getCtx
    case M.lookup n ctx of
        Just x  -> return x
        Nothing -> tcfail $ UnknownName n

freshTag :: TC Int
freshTag = lift $ lift (modify (+1) >> get)

runTC :: Int -> Ctx Meta Constrs' -> TC a -> Either TCFailure a
runTC maxTag ctx tc = evalState (runExceptT $ runReaderT tc ([], ctx)) maxTag

check :: Program Meta VoidConstrs -> Either TCFailure (Ctx Meta Constrs', Constrs)
check prog@(Prog defs) = runTC maxTag M.empty $ checkDefs (CS M.empty) defs
  where
    getTag (MVar i) = i
    getTag _        = 0  -- whatever, we're looking for maximum

    allTags = prog ^.. progRelevance . to getTag
    maxTag = L.maximum allTags

checkDefs :: Constrs -> [Def Meta VoidConstrs] -> TC (Ctx Meta Constrs', Constrs)
checkDefs cs [] = do
    ctx <- getCtx
    return (ctx, cs)
checkDefs cs (d:ds) = do
    Def n r ty mtm dcs <- with (bare d) $ checkDef d
    let dcs' = reduce <$> dcs
    with (Def n r ty mtm dcs')
        $ checkDefs (fromMaybe noConstrs dcs' `union` cs) ds
  where
    bare (Def n r ty mtm Nothing) = Def n r ty mtm Nothing

checkDef :: Def Meta VoidConstrs -> TC (Def Meta Constrs')
checkDef (Def n r ty Abstract Nothing) = return $ Def n r ty Abstract Nothing
checkDef (Def n r ty (Term tm) Nothing) = bt ("DEF-TERM", n) $ do
    (tmty, tmcs) <- checkTm tm
    tycs <- conv ty tmty
    let cs = tycs /\ tmcs
    return $ Def n r ty (Term tm) (Just cs)

checkDef (Def n r ty (Clauses cls) Nothing) = bt ("DEF-CLAUSES", n) $ do
    tcfail $ NotImplemented "checking def-clauses"

checkTm :: Term -> TC (Type, Constrs)

checkTm t@(V n) = bt ("VAR", n) $ do
    Def _n r ty mtm mcs <- lookup n
    return (ty, Fixed R --> r)

checkTm t@(I n ty) = bt ("INST", n, ty) $ do
    Def _n r ty' _mtm (fromMaybe noConstrs -> cs') <- instantiate freshTag IM.empty =<< lookup n
    convCs <- conv ty' ty
    -- we do not include (Fixed R --> r) because it will be an instance
    -- of this function that's runtime-relevant, not the function itself
    return (ty', cs' /\ convCs)

checkTm t@(Bind Lam (Def n r ty Abstract Nothing) tm) = bt ("LAM", t) $ do
    (tmty, tmcs) <- with (Def n r ty Abstract Nothing) $ checkTm tm
    return (Bind Pi (Def n r ty Abstract Nothing) tmty, tmcs)

checkTm t@(Bind Pi (Def n r ty Abstract Nothing) tm) = bt ("PI", t) $ do
    (tmty, tmcs) <- with (Def n r ty Abstract Nothing) $ checkTm tm
    return (Type, tmcs)

checkTm t@(App app_r f x) = bt ("APP", t) $ do
    (fty, fcs) <- checkTm f
    (xty, xcs) <- checkTm x
    case fty of
        Bind Pi (Def n' pi_r ty' Abstract Nothing) retTy -> do
            tycs <- conv xty ty'
            let cs =
                    tycs
                    /\ fcs
                    /\ cond pi_r xcs
                    /\ pi_r <--> app_r
            return (subst n' x retTy, cs)

        _ -> do
            tcfail $ NonFunction f fty

checkTm t@(Bind Let (Def n r ty body Nothing) tm) = bt ("LET", t) $ do
    letcs <- case body of
        Term t -> do
            (valty, valcs) <- checkTm t
            tycs <- conv ty valty
            return $ Just (valcs /\ tycs)
        Abstract -> return Nothing
        Clauses cls -> error "trying to check let-bound clauses"

    (tmty, tmcs) <-
        with (Def n r ty body letcs)
            $ checkTm tm
    return (tmty, tmcs /\ fromMaybe noConstrs letcs)

checkTm (Forced tm) = checkTm tm
checkTm Erased = return (Erased, noConstrs)
checkTm Type   = return (Type,   noConstrs)

newtype TC' a = LiftTC' { runTC' :: TC a } deriving (Functor, Applicative, Monad)
type ITC = StateT (IM.IntMap Int) TC'

freshen :: Monad m => m Int -> Meta -> StateT (IM.IntMap Meta) m Meta
freshen freshTag m@(Fixed r) = return m
freshen freshTag (MVar i) = do
    imap <- get
    case IM.lookup i imap of
        Just j ->
            return j
        Nothing -> do
            j <- MVar <$> lift freshTag
            modify $ IM.insert i j
            return j

instantiate :: (Functor m, Monad m, CsRelevance cs) => m Int -> IM.IntMap Meta -> Def Meta cs -> m (Def Meta cs)
instantiate freshTag metaMap def = evalStateT refresh metaMap
  where
    refresh = defRelevance' csRelevance (freshen freshTag) def

-- left: from context (from outside), right: from expression (from inside)
conv :: Type -> Type -> TC Constrs
conv p q = do
    ctx <- getCtx
    conv' (whnf ctx p) (whnf ctx q)

-- note that this function gets arguments in WHNF
conv' :: Type -> Type -> TC Constrs

-- whnf is variable (something irreducible, constructor or axiom)
conv' (V n) (V n') = bt ("C-VAR", n, n') $ do
    require (n == n') $ Mismatch (show n) (show n')
    return noConstrs

conv' p@(Bind b (Def n r ty Abstract Nothing) tm) q@(Bind b' (Def n' r' ty' Abstract Nothing) tm')
    = bt ("C-BIND", p, q) $ do
        require (b == b') $ Mismatch (show b) (show b')
        xs <- conv ty (rename [n'] [n] ty')
        ys <- with (Def n r ty Abstract Nothing) $ conv tm (rename [n'] [n] tm')
        return $ xs /\ ys /\ r <--> r'

-- whnf is application (application of something irreducible)
conv' p@(App r f x) q@(App r' f' x') = bt ("C-APP", p, q) $ do
    xs <- conv f f'
    ys <- conv x x'
    return $ xs /\ ys /\ r <--> r'

{-
conv' p@(Let (Def n r ty mtm Nothing) tm) q@(Let (Def n' r' ty' mtm' Nothing) tm') = bt ("C-LET", p, q) $ do
    (val, val') <- case (mtm, mtm') of
        (Just t, Just t') -> return (t, t')
        (Nothing, Nothing) -> return (Erased, Erased)
        _ -> tcfail $ Mismatch (show mtm) (show mtm')

    xs <- conv ty (rename [n'] [n] ty')
    (valty, valcs) <- checkTm val
    tycs <- conv ty valty
    vcs <- conv val val'
    let letcs = valcs /\ tycs
    ys <- with (Def n r ty mtm (Just letcs)) $ conv tm (rename [n'] [n] tm')
    return $ letcs /\ ys /\ vcs /\ r <--> r'
-}

conv' (Forced l) (Forced r) = conv l r
conv' Type   Type   = return noConstrs
conv' Erased Erased = return noConstrs

conv' p q = tcfail $ CantConvert p q

rename :: [Name] -> [Name] -> TTmeta -> TTmeta
rename [] [] tm = tm
rename (n : ns) (n' : ns') tm = rename ns ns' $ subst n (V n') tm
rename _ _ _ = error "rename: incoherent args"
