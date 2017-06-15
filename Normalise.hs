{-# LANGUAGE ConstraintKinds, ViewPatterns #-}
module Normalise (IsRelevance, Form(..), red, whnf, nf) where

import TT
import TTUtils
import Pretty

import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M

--import Debug.Trace

type IsRelevance r = (PrettyR r, Eq r)

data Form = NF | WHNF deriving Show

data Match a = Yes a | No | Stuck deriving Show

instance Functor Match where
    fmap f (Yes x) = Yes (f x)
    fmap f No = No
    fmap f Stuck = Stuck

instance Applicative Match where
    pure = Yes
    Yes f <*> Yes x = Yes (f x)
    Yes f <*> No = No
    Yes f <*> Stuck = Stuck
    No <*> _ = No
    Stuck <*> No = No
    Stuck <*> _ = Stuck

instance Alternative Match where
    empty = No
    Yes x <|> _ = Yes x
    No <|> y = y
    Stuck <|> _ = Stuck

instance Monad Match where
    return = Yes
    Yes x >>= f = f x
    No >>= f = No
    Stuck >>= f = Stuck

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

pruneLet :: TT r -> TT r
pruneLet (Bind Let ds rhs) = Bind Let [d | d <- ds, defName d `S.member` reachableFrom (freeVars rhs)] rhs
  where
    reachableFrom :: S.Set Name -> S.Set Name
    reachableFrom orig
        | new `S.isSubsetOf` orig = orig
        | otherwise = reachableFrom $ S.union orig new
      where
        new = S.unions [freeVars d | d <- ds, defName d `S.member` orig]
pruneLet tm = tm

red :: IsRelevance r => Form -> Ctx r -> TT r -> TT r

red form ctx t@(V Blank) = t

red form ctx t@(V n)
    | Just (Def _n r ty body cs) <- M.lookup n ctx
    = case body of
        Abstract _  -> t
        Term     tm -> red form ctx tm
        Clauses [Clause [] (PV _) rhs] -> red form ctx rhs  -- constant function
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
    | otherwise = simplLet . pruneLet $ Bind Let ds reducedTm
  where
    reducedTm = red form (insertDefs ds ctx) tm

-- The remaining binders are Pi and Lam.
red WHNF ctx t@(Bind b ds tm) = t  -- this is in WHNF already
red  NF  ctx t@(Bind b [] tm) = Bind b [] $ red NF ctx tm
red  NF  ctx t@(Bind b (d:ds) tm)
    = Bind b (redDef NF ctx d : ds') tm'
  where
    Bind _b ds' tm' = red NF (M.insert (defName d) d ctx) $ Bind b ds tm

red form ctx t@(App r f (Bind Let ds tm))
    = case clashingNames of
        [] -> red form ctx $ Bind Let ds (App r f tm)
        _  -> error $ "app+let reduction R: capture avoidance not implemented yet: " ++ show clashingNames
  where
    clashingNames = [defName d | d <- ds, defName d `occursIn` f]

red form ctx t@(App r (Bind Let ds tm) x)
    = case clashingNames of
        [] -> red form ctx $ Bind Let ds (App r tm x)
        _  -> error $ "app+let reduction L: capture avoidance not implemented yet: " ++ show clashingNames
  where
    clashingNames = [defName d | d <- ds, defName d `occursIn` x]

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
    , Just (defBody -> Clauses cs) <- M.lookup fn ctx
    , Yes rhs <- firstMatch $ map (matchClause ctx fn t) cs
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

-- This function takes a disassembled pattern and a term application
-- and tries to match them up, while ensuring that there are at least
-- as many terms as there are patterns. Any superfluous terms are returned.
matchUp :: [(r, Pat r)] -> [(r, TT r)]
    -> Match ([(Pat r, TT r)], [(r, TT r)])

matchUp ((_pr, pat):ps) ((_tr, tm):ts)
    = do
        (pts, rest) <- matchUp ps ts
        return ((pat,tm):pts, rest)

matchUp [] ts = Yes ([], ts)

matchUp ps [] = No

matchClause :: IsRelevance r => Ctx r -> Name -> TT r -> Clause r -> Match (TT r)
matchClause ctx fn tm (Clause pvs lhs rhs) = do
    -- check that the matched term is actually an invocation of the given function
    () <- case tmH of
            V fn' | fn' == fn
                -> Yes ()
            _
                -> Stuck

    -- first, match up patterns vs. terms, keeping superfluous terms
    -- (if application is oversaturated)
    (pts, extraTerms) <- matchUp pargs args

    -- get the matching substitution
    pvSubst <- M.unionsWith (\_ _ -> error "nonlinear pattern")
        <$> sequence [match pvs' ctx p $ red WHNF ctx tm | (p,tm) <- pts]

    -- substitute in RHS, and then tack on the superfluous terms
    return $
        mkApp
            (safeSubst pvs [pvSubst M.! defName d | d <- pvs] rhs)
            extraTerms
  where
    (_patH, pargs) = unApplyPat lhs
    ( tmH,  args)  = unApply tm
    pvs' = M.fromList [(defName d, d) | d <- pvs]

safeSubst :: [Def r] -> [TT r] -> TT r -> TT r
safeSubst [] [] rhs = rhs
safeSubst (d:ds) (t:ts) rhs
    = safeSubst ds' ts rhs'
  where
    (ds', rhs') = substBinder (defName d) t ds rhs
safeSubst _ _ rhs = error $ "safeSubst: defs vs. terms do not match up"

match :: IsRelevance r => Ctx r -> Ctx r -> Pat r -> TT r -> Match (M.Map Name (TT r))
match pvs ctx (PV Blank) tm'
    = Yes M.empty

match pvs ctx (PV n) tm'
    | Just (defBody -> Abstract Var) <- M.lookup n pvs
    = Yes $ M.singleton n tm'

match pvs ctx (PV n) (V n')
    | n == n'
    , Just (defBody -> Abstract Postulate) <- M.lookup n ctx
    = Yes M.empty

match pvs ctx (PApp r f x) (App r' f' x')
    = M.unionWith (\_ _ -> error "non-linear pattern")
        <$> match pvs ctx f f'
        <*> match pvs ctx x (red WHNF ctx x')

match pvs ctx (PForced tm) tm'
    = Yes M.empty

match pvs ctx (PForcedCtor n) (V n')
    | Just (defBody -> Abstract Postulate) <- M.lookup n' ctx  -- check n' is /some/ constructor
    = Yes M.empty

match pvs ctx pat (V n)
    | Just d <- M.lookup n ctx
    = case defBody d of
        Abstract Var -> Stuck  -- variables may or may not match as we learn what they are
        Abstract (Foreign _) -> Stuck  -- foreigns are variables, really
        _ -> No

match _ _ _ _ = No

firstMatch :: Alternative f => [f a] -> f a
firstMatch = foldr (<|>) empty
