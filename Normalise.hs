{-# LANGUAGE ConstraintKinds #-}
module Normalise (IsRelevance, Form(..), red, whnf, nf) where

import TT
import Pretty

import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

type IsRelevance r = (PrettyR r, Eq r)

data Form = NF | WHNF deriving Show

dbg :: Show a => a -> b -> b
-- dbg = traceShow
dbg _ x = x

dbgS :: (Show a, Show b) => a -> b -> b
dbgS x y = (x, y) `dbg` y

whnf :: IsRelevance r => Ctx r cs -> TT r -> TT r
whnf = red WHNF

nf :: IsRelevance r => Ctx r cs -> TT r -> TT r
nf = red NF

redDef :: IsRelevance r => Form -> Ctx r cs -> Def r cs' -> Def r cs'
redDef form ctx (Def n r ty body cs) = Def n r (red form ctx ty) (redBody form ctx body) cs

redBody :: IsRelevance r => Form -> Ctx r cs -> Body r -> Body r
redBody form ctx (Abstract a)  = Abstract a
redBody form ctx (Term tm)     = Term (red form ctx tm)
redBody NF   ctx (Patterns cf) = Patterns (redCaseFun NF ctx cf)
redBody WHNF ctx body@(Patterns cf) = body

redCaseFun :: IsRelevance r => Form -> Ctx r cs -> CaseFun r -> CaseFun r
redCaseFun NF ctx (CaseFun args ct) = go ctx [] args
  where
    go ctx rargs [] = CaseFun (reverse rargs) (redCaseTree NF ctx ct)
    go ctx rargs (d:ds) =
        let d' = csDef $ redDef NF ctx d
          in go (M.insert (defName d) d' ctx) (d':rargs) ds

redCaseTree :: IsRelevance r => Form -> Ctx r cs -> CaseTree r -> CaseTree r
redCaseTree NF ctx (PlainTerm tm) = PlainTerm $ red NF ctx tm
redCaseTree NF ctx (Case v alts) = Case v $ map (redAlt NF ctx) alts

redAlt :: IsRelevance r => Form -> Ctx r cs -> Alt r -> Alt r
redAlt NF ctx (Alt lhs rhs) = Alt (redAltLHS NF ctx lhs) (redCaseTree NF ctx rhs)

redAltLHS :: IsRelevance r => Form -> Ctx r cs -> AltLHS r -> AltLHS r
redAltLHS NF ctx Wildcard = Wildcard
redAltLHS NF ctx (Ctor cn args eqs) = Ctor cn (map (redDef NF ctx) args) [(n, red NF ctx tm) | (n, tm) <- eqs]

red :: IsRelevance r => Form -> Ctx r cs -> TT r -> TT r

red form ctx t@(V Blank) = t

red form ctx t@(V n)
    | Just (Def _n r ty body cs) <- M.lookup n ctx
    = case body of
        Abstract _  -> t
        Term     tm -> red form ctx tm
        Patterns cf -> t

    | otherwise = error $ "unknown variable: " ++ show n  -- unknown variable

red form ctx t
    | ("REDUCING", form, t, M.keys ctx) `dbg` False
    = undefined

red form ctx t@(I n i) = red form ctx (V n)

red form ctx t@(Bind Let (Def n r ty body Nothing) tm)
    = red form (M.insert n (Def n r ty body Nothing) ctx) tm

red WHNF ctx t@(Bind b d tm) = t
red  NF  ctx t@(Bind b d tm) = Bind b (redDef NF ctx d) (red NF ctx' tm)
  where
    Def n r ty body Nothing = d
    ctx' = M.insert n (Def n r ty body Nothing) ctx

-- pattern-matching definitions
red form ctx t@(App r f x)
    | (V fn, _args) <- unApply t
    , Just (Def _ _ _ (Patterns cf) _) <- M.lookup fn ctx
    = fromMaybe t $ evalPatterns form ctx cf t

-- we reduce specialised terms as non-specialised terms
red form ctx t@(App r f x)
    | (I fn _ty, args) <- unApply t
    = red form ctx (mkApp (V fn) args)

red WHNF ctx t@(App r f x)
    -- lambdas
    | Bind Lam (Def n' r' ty' (Abstract Var) Nothing) tm' <- redF
    = red WHNF ctx $ subst n' x tm'

    -- everything else
    | otherwise = t  -- not a redex
  where
    redF = red WHNF ctx f

red NF ctx t@(App r f x)
    | Bind Lam (Def n' r' ty' (Abstract Var) Nothing) tm' <- redF
    = red NF ctx $ subst n' redX tm'

    | otherwise = App r redF redX  -- not a redex
  where
    redF = red NF ctx f
    redX = red NF ctx x

substVars :: Ctx r cs -> [Def r cs'] -> [(r, TT r)] -> Maybe (Ctx r cs, [(r, TT r)])
substVars ctx [] args = Just (ctx, args)
substVars ctx ds []   = Nothing  -- not enough args to reduce
substVars ctx (d:ds) ((_,arg):args)
    = let d' = d{ defBody = Term arg, defConstraints = Nothing }
        in substVars (M.insert (defName d) d' ctx) ds args

evalPatterns :: IsRelevance r => Form -> Ctx r cs -> CaseFun r -> TT r -> Maybe (TT r)
evalPatterns form ctx (CaseFun argvars ct) tm = do
    (argCtx, extras) <- substVars M.empty argvars argvals
    rhs <- evalCaseTree form ctx $ substCtxTree argCtx ct
    return $ red form ctx (mkApp rhs extras)
  where
    (V _fn, argvals) = unApply tm

evalCaseTree :: IsRelevance r => Form -> Ctx r cs -> CaseTree r -> Maybe (TT r)
evalCaseTree form ctx (PlainTerm tm) = Just $ red form ctx tm
evalCaseTree form ctx (Case tm alts)
    = firstMatch $ map (evalAlt form ctx tm') alts
  where
    tm' = red WHNF ctx tm

firstMatch :: Alternative f => [f a] -> f a
firstMatch = foldr (<|>) empty

-- here, the term tm is in WHNF
evalAlt :: IsRelevance r => Form -> Ctx r cs -> TT r -> Alt r -> Maybe (TT r)
evalAlt form ctx tm (Alt lhs rhs) = do
    matchCtx <- match lhs tm
    evalCaseTree form (matchCtx `M.union` ctx) (substCtxTree matchCtx rhs)

substCtxTree :: Ctx r cs -> CaseTree r -> CaseTree r
substCtxTree ctx ct = foldr substOne ct (M.elems ctx)
  where
    substOne (Def n r ty (Term tm) Nothing) ct = substCaseTree n tm ct

match :: AltLHS r -> TT r -> Maybe (Ctx r cs)
match Wildcard _ = Just M.empty
match (Ctor cn argvars eqs) tm
    | (V cn', argvals) <- unApply tm
    , cn == cn'
    = do
        (ctx, []) <- substVars M.empty argvars argvals
        return ctx

match _ _ = Nothing


{-
appDepth :: TT r -> Int
appDepth (App r f x) = 1 + appDepth f
appDepth _ = 0

unwrap :: Int -> TT r -> (TT r, [(r, TT r)])
unwrap 0 tm = (tm, [])
unwrap n (App r f x) = (tm, xs ++ [(r, x)])
  where
    (tm, xs) = unwrap (n-1) f
unwrap n tm = error $ "can't unwrap"

rewrap :: TT r -> [(r, TT r)] -> TT r
rewrap f [] = f
rewrap f ((r, x) : xs) = rewrap (App r f x) xs

data Tri a = Yep a | Nope | Unknown deriving (Eq, Ord, Show)

instance Functor Tri where
    fmap f (Yep x) = Yep (f x)
    fmap f Nope    = Nope
    fmap f Unknown = Unknown

instance Applicative Tri where
    pure = Yep
    Yep f <*> Yep x = Yep (f x)
    Unknown <*> _ = Unknown
    _ <*> Unknown = Unknown
    Nope <*> _ = Nope
    _ <*> Nope = Nope

triJoin :: Tri (Tri a) -> Tri a
triJoin Unknown = Unknown
triJoin Nope    = Nope
triJoin (Yep x)  = x

instance Monad Tri where
    return = Yep
    x >>= f = triJoin $ fmap f x

redClauses :: IsRelevance r => Form -> Ctx r cs -> [Clause r] -> TT r -> TT r
redClauses form ctx [] tm = tm
redClauses form ctx (c : cs) tm
    = case redClause' form ctx (freshen ctx c) tm of
        Yep tm' -> tm'
        Nope    -> redClauses form ctx cs tm
        Unknown -> tm

redClause' :: IsRelevance r => Form -> Ctx r cs -> Clause r -> TT r -> Tri (TT r)
redClause' form ctx c tm
    | ("RED-CLAUSE", M.keys ctx, c, tm) `dbg` False
    = undefined
redClause' form ctx (Clause pvs lhs rhs) tm
    | tmDepth < patDepth = Unknown  -- undersaturated

    | otherwise = do
        patSubst <- matchTm form patVars lhs tm'
        let patValues = patSubst `M.union` ctx
        let diff = M.keysSet patVars `S.difference` M.keysSet patValues
        if not (S.null diff)
            then error $ "pattern vars not bound in match: " ++ intercalate ", " (map show $ S.toList diff)
            else return ()
        return . red form ctx $ rewrap (substMany patSubst rhs) extra
  where
    patDepth = pappDepth lhs
    tmDepth = appDepth tm
    (tm', extra) = unwrap (tmDepth - patDepth) tm
    patVars = foldr (M.insert <$> defName <*> csDef) ctx pvs

matchTms :: IsRelevance r => Form -> Ctx r cs -> [Pat r] -> [TT r] -> Tri (Ctx r cs)
matchTms form ctx ls rs = do
    ss <- zipWithM (matchTm form ctx) ls rs
    let joined = M.unions ss
    if M.size joined == sum (map M.size ss)
        then return joined  -- all OK
        else do
            let badvars = S.unions [S.intersection (M.keysSet p) (M.keysSet q) | (p, qs) <- lup ss, q <- qs]
            error $ "multiple occurrence of patvars: " ++ intercalate ", " (map show $ S.toList badvars)

lup :: [a] -> [(a, [a])]
lup [] = []
lup [x] = []
lup (x : ys) = (x, ys) : lup ys

matchTm :: IsRelevance r => Form -> Ctx r cs -> Pat r -> TT r -> Tri (Ctx r cs)
matchTm form ctx pat tm
    | ("MATCH-TM", pat, tm, M.keys ctx) `dbg` False
    = undefined

-- the blank pattern matches everything, generates nothing
matchTm form ctx (PV Blank) tm = Yep M.empty

-- patvars match anything
matchTm form ctx (PV n) tm
    | Just d@(Def n r ty (Abstract Var) Nothing) <- M.lookup n ctx
    = Yep $ M.singleton n (Def n r ty (Term tm) Nothing)

-- data constructors match
matchTm form ctx pat@(PApp _ _ _) tm@(App _ _ _)
    | (PV cn , args ) <- patUnApply pat
    , (V  cn', args') <- unApply tm
    , cn == cn'  -- heads are the same
--    , Just (Def _ _ _ (Abstract Postulate) Nothing) <- M.lookup cn ctx  -- is a ctor/postulate
    = matchTms form ctx (map snd args) (map (red form ctx . snd) args')

-- forced patterns always match, not generating anything
matchTm form ctx (PForced _) tm
    = Yep M.empty

-- no match otherwise
matchTm form ctx _ _ = Nope

freshen :: Ctx r cs -> Clause r -> Clause r
freshen ctx (Clause [] lhs rhs) = Clause [] lhs rhs
freshen ctx (Clause (d:ds) lhs rhs)
    | n `M.member` ctx
    = let n' = getFreshName ctx n
        in Clause (d{ defName = n' } :ds') (patRename n n' lhs') (rename n n' rhs')
    | otherwise = Clause (d:ds') lhs' rhs'
  where
    n = defName d
    Clause ds' lhs' rhs' = freshen ctx $ Clause ds lhs rhs

-- TODO: remove `Forced` from matched contexts
-}
