{-# LANGUAGE ConstraintKinds #-}
module Normalise (IsRelevance, Form(..), red, whnf, nf) where

import TT
import TTUtils
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

whnf :: IsRelevance r => Ctx r -> TT r -> TT r
whnf = red WHNF

nf :: IsRelevance r => Ctx r -> TT r -> TT r
nf = red NF

redDef :: IsRelevance r => Form -> Ctx r -> Def r -> Def r
redDef form ctx (Def n r ty body cs) = Def n r (red form ctx ty) (redBody form ctx body) cs

redBody :: IsRelevance r => Form -> Ctx r -> Body r -> Body r
redBody form ctx (Abstract a)  = Abstract a
redBody form ctx (Term tm)     = Term (red form ctx tm)

red :: IsRelevance r => Form -> Ctx r -> TT r -> TT r

red form ctx t@(V Blank) = t

red form ctx t@(V n)
    | Just (Def _n r ty body cs) <- M.lookup n ctx
    = case body of
        Abstract _  -> t
        Term     tm -> red form ctx tm

    | otherwise = error $ "unknown variable: " ++ show n  -- unknown variable

red form ctx t
    | ("REDUCING", form, t, M.keys ctx) `dbg` False
    = undefined

red form ctx t@(I n i) = red form ctx (V n)

red form ctx t@(Bind Let d tm)
    = case defBody d of
        Abstract Var
            -> error "trying to substitute a variable"
        Abstract Postulate
            -> red form ctx' tm
        Term val
            -- we insert stuff into the context for recursive definitions
            -- and substitute for WHNF unevaluated terms
            -> red form ctx' $ subst (defName d) val tm
  where
    ctx' = M.insert (defName d) d ctx

red WHNF ctx t@(Bind b d tm) = t
red  NF  ctx t@(Bind b d tm) = Bind b (redDef NF ctx d) (red NF ctx' tm)
  where
    ctx' = M.insert (defName d) d ctx

red form ctx t@(App r f x)
    -- lambdas
    | Bind Lam (Def n' r' ty' (Abstract Var) cs) tm' <- redF
    = red form ctx $ subst n' redX tm'

    -- everything else
    | otherwise = App r redF redX  -- not a redex
  where
    redF = red NF ctx f
    redX = case form of
        NF   -> red NF ctx x
        WHNF -> x

red NF ctx t@(Case r s ty alts) = 
    case firstMatch $ map (evalAlt NF ctx sWHNF) alts of
        Just nf -> nf
        Nothing ->
            t -- Case r (red NF ctx s) (red NF ctx ty) (map (redAltNF ctx) alts)
  where
    sWHNF = red WHNF ctx s

red WHNF ctx t@(Case r s ty alts) = 
    case firstMatch $ map (evalAlt WHNF ctx sWHNF) alts of
        Just nf -> nf
        Nothing -> t
  where
    sWHNF = red WHNF ctx s

redAltNF :: IsRelevance r => Ctx r -> Alt r -> Alt r
redAltNF ctx (Alt Wildcard rhs) = Alt Wildcard $ red NF ctx rhs
redAltNF ctx (Alt lhs@(Ctor cn args eqs) rhs)
    = Alt lhs $ red NF ctx' rhs
  where
    ctx' = foldr (\d -> M.insert (defName d) d) ctx args

{-
substArgs :: Termy f => [Def r] -> [(r, TT r)] -> f r -> f r
substArgs []     []         rhs = rhs
substArgs (d:ds) ((r,v):vs) rhs = subst
substArgs (d:ds) ((r,v):vs) rhs = substArgs ds' vs rhs'
  where
    (ds', [], rhs') = substBinder (defName d) v ds [] rhs
-}

argSubst :: [Def r] -> [(r, TT r)] -> [(Name, TT r)]
argSubst = zipWith $ \d (r,v) -> (defName d, v)

firstMatch :: Alternative f => [f a] -> f a
firstMatch = foldr (<|>) empty

-- here, the scrutinee (tm) is in WHNF
evalAlt :: IsRelevance r => Form -> Ctx r -> TT r -> Alt r -> Maybe (TT r)
evalAlt form ctx tm (Alt Wildcard rhs)
    = return $ red form ctx rhs

evalAlt form ctx tm (Alt (Ctor cn argvars eqs) rhs)
    | (V cn', argvals) <- unApply tm
    , cn' == cn
    , length argvars == length argvals
    = Just . red form ctx
        $ substs (argSubst argvars argvals) rhs

evalAlt form ctx tm (Alt (Ctor cn argvars eqs) rhs)
    | (V cn', argvals) <- unApply tm
    , cn' == cn
    , length argvars /= length argvals
    = error "constructor arity mismatch in pattern"

evalAlt form ctx tm alt = Nothing
