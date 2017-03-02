{-# LANGUAGE ConstraintKinds #-}
module Normalise (IsRelevance, Form(..), red, whnf, nf) where

import TT
import TTUtils
import Pretty

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
redBody form ctx (Abstract a) = Abstract a
redBody form ctx (Term tm)    = Term (red form ctx tm)
redBody NF   ctx (Clauses cs) = Clauses $ map (redClause NF ctx) cs
redBody WHNF ctx body@(Clauses cs) = body

redClause :: IsRelevance r => Form -> Ctx r -> Clause r -> Clause r
redClause NF ctx (Clause pvs lhs rhs) =
    Clause
        (map (redDef NF ctx) pvs)
        (redPat NF ctx lhs)
        (red NF ctx rhs)
redClause _ ctx clause = error $ "redClause non-NF"

redPat :: IsRelevance r => Form -> Ctx r -> Pat r -> Pat r
redPat NF ctx (PApp r f x) = PApp r (redPat NF ctx f) (redPat NF ctx x)
redPat NF ctx tm@(PV _)    = tm
redPat NF ctx (PForced tm) = PForced $ red NF ctx tm
redPat _ ctx pat = error $ "redPat non-NF"

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
        Clauses  cs -> t

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
    | or [defName d `occursIn` x | d <- ds]
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
    , Just (Def _ _ _ (Clauses cs) _) <- M.lookup fn ctx
    , Just rhs <- firstMatch $ map (matchClause t) cs
    = red form ctx rhs

    -- everything else
    | otherwise
    = redT  -- not a redex
  where
    redT = App r redF redX
    redF = red form ctx f
    redX = case form of
        NF   -> red NF ctx x
        WHNF -> x

matchClause :: PrettyR r => TT r -> Clause r -> Maybe (TT r)
matchClause tm (Clause pvs lhs rhs)
    = substs . M.toList <$> match lhs tm <*> pure rhs

match :: PrettyR r => Pat r -> TT r -> Maybe (M.Map Name (TT r))
match (PV n) tm' = Just $ M.singleton n tm'
match (PApp r f x) (App r' f' x')
    = M.unionWith (\_ _ -> error "non-linear pattern")
        <$> match f f'
        <*> match x x'
match (PForced tm) tm' = Just $ M.empty
match _ _ = Nothing

firstMatch :: Alternative f => [f a] -> f a
firstMatch = foldr (<|>) empty
