{-# LANGUAGE ConstraintKinds #-}
module Normalise (IsRelevance, Form(..), red, whnf, nf) where

import TT
import TTUtils
import Pretty

import Data.Maybe
import Control.Applicative
import qualified Data.Map as M

--import Debug.Trace

type IsRelevance r = (PrettyR r, Eq r)

data Form = NF | WHNF deriving Show

--dbg :: Show a => a -> b -> b
--dbg = traceShow
dbg :: a -> b -> b
dbg _ x = x

--dbgS :: (Show a, Show b) => a -> b -> b
--dbgS x y = (x, y) `dbg` y

whnf :: IsRelevance r => Ctx r -> TT r -> TT r
whnf = red WHNF

nf :: IsRelevance r => Ctx r -> TT r -> TT r
nf = red NF

redDef :: IsRelevance r => Form -> Ctx r -> Def r -> Def r
redDef form ctx (Def n r ty body cs) = Def n r (red form ctx ty) (redBody form ctx body) cs

redBody :: IsRelevance r => Form -> Ctx r -> Body r -> Body r
redBody form ctx (Abstract a)  = Abstract a
redBody form ctx (Term tm)     = Term (red form ctx tm)
redBody NF   ctx (Patterns cf) = Patterns (redCaseFun NF ctx cf)
redBody WHNF ctx body@(Patterns cf) = body

redCaseFun :: IsRelevance r => Form -> Ctx r -> CaseFun r -> CaseFun r
redCaseFun NF ctx (CaseFun args ct) = go ctx [] args
  where
    go ctx rargs [] = CaseFun (reverse rargs) (redCaseTree NF ctx ct)
    go ctx rargs (d:ds) =
        let d' = redDef NF ctx d
          in go (M.insert (defName d) d' ctx) (d':rargs) ds

redCaseFun WHNF ctx cf = error "impossible: redCaseFun WHNF"

redCaseTree :: IsRelevance r => Form -> Ctx r -> CaseTree r -> CaseTree r
redCaseTree NF ctx (Leaf tm) = Leaf $ red NF ctx tm
redCaseTree NF ctx (Case r v alts) = Case r v $ map (redAlt NF ctx) alts
redCaseTree WHNF ctx ct = error "impossible: redCaseTree WHNF"

redAlt :: IsRelevance r => Form -> Ctx r -> Alt r -> Alt r
redAlt NF ctx (Alt lhs rhs) = Alt (redAltLHS NF ctx lhs) (redCaseTree NF ctx rhs)
redAlt WHNF ctx alt = error "impossible: redAlt WHNF"

redAltLHS :: IsRelevance r => Form -> Ctx r -> AltLHS r -> AltLHS r
redAltLHS NF ctx Wildcard = Wildcard
redAltLHS NF ctx (Ctor r cn args eqs)
    = Ctor r cn (map (redDef NF ctx) args) [(n, red NF ctx tm) | (n, tm) <- eqs]
redAltLHS WHNF ctx lhs = error "impossible: redAltLHS WHNF"

simplLet :: TT r -> TT r
simplLet (Bind Let [] tm) = tm
simplLet tm = tm

red :: IsRelevance r => Form -> Ctx r -> TT r -> TT r

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

-- empty let binding
red form ctx t@(Bind Let [] tm) = red form ctx tm
red form ctx t@(Bind Let ds tm)
    -- some progress: try again
    | reducedTm /= tm  = red form ctx $ Bind Let ds reducedTm

    -- no progress: stop trying and go back
    | otherwise = simplLet $ Bind Let [d | d <- ds, defName d `occursIn` reducedTm] reducedTm
  where
    reducedTm = red form (insertDefs ds ctx) tm

-- The remaining binders are Pi and Lam.
red WHNF ctx t@(Bind b ds tm) = t  -- this is in WHNF already
red  NF  ctx t@(Bind b [] tm) = Bind b [] $ red NF ctx tm
red  NF  ctx t@(Bind b (d:ds) tm)
    = Bind b (redDef NF ctx d : ds') tm'
  where
    Bind _b ds' tm' = red NF (M.insert (defName d) d ctx) $ Bind b ds tm

red form ctx t@(App r (Bind Let ds tm) x)
    | or [defName d `occursIn` tm | d <- ds]
        = error $ "app+let reduction: capture avoidance not implemented yet"
    | otherwise
        = red form ctx $ Bind Let ds (App r tm x)

red form ctx t@(App r f x)
    -- simple lambda
    | Bind Lam (Def n' r' ty' (Abstract Var) cs : ds) tm' <- redF
    = let tm'' = red form ctx $ subst n' redX tm'
        in case ds of
            [] -> tm''
            _  -> Bind Lam ds tm''

    -- pattern matching instance reduces as variable
    | (I fn _, args) <- unApply t
    = red form ctx $ mkApp (V fn) args

    -- pattern-matching definitions
    | (V fn, args) <- unApply t
    , Just (Def _ _ _ (Patterns cf) _) <- M.lookup fn ctx
    , length args == length (cfArgs cf)
    = fromMaybe redT $ (red form ctx <$> evalPatterns form ctx cf redT)

    -- everything else
    | otherwise
    = redT  -- not a redex
  where
    redT = App r redF redX
    redF = red form ctx f
    redX = case form of
        NF   -> red NF ctx x
        WHNF -> x

red form ctx (Forced tm) = red form ctx tm

substArgs :: Termy f => [Def r] -> [(r, TT r)] -> f r -> Maybe (f r, [(r, TT r)])
substArgs []     extras rhs = Just (rhs, extras)
substArgs (d:ds) []     rhs = Nothing  -- ran out of values
substArgs (d:ds) ((r,v):vs) rhs =
    substArgs ds' vs rhs'
  where
    (ds', [], rhs') = substBinder n v ds [] rhs
    n = defName d

evalPatterns :: IsRelevance r => Form -> Ctx r -> CaseFun r -> TT r -> Maybe (TT r)
evalPatterns form ctx (CaseFun argvars ct) tm = do
    (ct', extras) <- substArgs argvars argvals ct
    rhs <- evalCaseTree form ctx ct'
    return $ red form ctx (mkApp rhs extras)
  where
    (V _fn, argvals) = unApply tm

evalCaseTree :: IsRelevance r => Form -> Ctx r -> CaseTree r -> Maybe (TT r)
evalCaseTree form ctx (Leaf tm) = Just $ red form ctx tm
evalCaseTree form ctx (Case r tm alts)
    = firstMatch $ map (evalAlt form ctx tm') alts
  where
    tm' = red form ctx tm

firstMatch :: Alternative f => [f a] -> f a
firstMatch = foldr (<|>) empty

-- here, the term tm is in WHNF
evalAlt :: IsRelevance r => Form -> Ctx r -> TT r -> Alt r -> Maybe (TT r)
evalAlt form ctx tm (Alt Wildcard rhs)
    = evalCaseTree form ctx rhs

evalAlt form ctx tm (Alt (Ctor r cn argvars eqs) rhs)
    | (V cn', argvals) <- unApply tm
    , cn' == cn
    = do
        (rhs', []) <- substArgs argvars argvals rhs
        evalCaseTree form ctx rhs'

evalAlt form ctx tm alt = Nothing
