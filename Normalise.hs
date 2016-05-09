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
redCaseTree NF ctx (Leaf tm) = Leaf $ red NF ctx tm
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
evalCaseTree form ctx (Leaf tm) = Just $ red form ctx tm
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
