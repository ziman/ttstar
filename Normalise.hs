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
            -> red form (M.insert (defName d) d ctx) tm
        Term val
            -> red form ctx $ subst (defName d) val tm

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

red form ctx t@(Case r s ty alts) = 
    case firstMatch $ map (evalAlt form ctx sWHNF) alts of
        Just nf -> nf
        Nothing -> error $ "pattern match failure: " ++ show t
  where
    sWHNF = red WHNF ctx s

substArgs :: Termy f => [Def r] -> [(r, TT r)] -> f r -> Maybe (f r, [(r, TT r)])
substArgs []     extras rhs = Just (rhs, extras)
substArgs (d:ds) []     rhs = Nothing  -- ran out of values
substArgs (d:ds) ((r,v):vs) rhs =
    substArgs ds' vs rhs'
  where
    (ds', [], rhs') = substBinder n v ds [] rhs
    n = defName d

firstMatch :: Alternative f => [f a] -> f a
firstMatch = foldr (<|>) empty

-- here, the scrutinee (tm) is in WHNF
evalAlt :: IsRelevance r => Form -> Ctx r -> TT r -> Alt r -> Maybe (TT r)
evalAlt form ctx tm (Alt Wildcard rhs)
    = return $ red form ctx rhs

evalAlt form ctx tm (Alt (Ctor cn argvars eqs) rhs)
    | (V cn', argvals) <- unApply tm
    , cn' == cn
    = do
        (rhs', []) <- substArgs argvars argvals rhs
        return $ red form ctx rhs'

evalAlt form ctx tm alt = Nothing
