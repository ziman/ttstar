{-# LANGUAGE ConstraintKinds, ViewPatterns, Rank2Types #-}
module TT.Normalise (IsRelevance, Form(..), red, whnf, nf) where

import TT.Core
import TT.Utils
import TT.Pretty

import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M

import Control.Monad.Trans.Writer.Lazy

--import Debug.Trace

type IsRelevance r = (PrettyR r, Eq r, Ord r)

newtype CM r = CM (Constrs r)
instance Ord r => Monoid (CM r) where
    mempty = CM M.empty
    mappend (CM l) (CM r) = CM $ M.unionWith S.union l r

type RMT m r a = WriterT m (CM r) a
type RM r a = Writer (CM r) a
type Red f = forall r. (IsRelevance r) => Ctx r -> f r -> RM r (f r)

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

whnf :: Red TT
whnf = red WHNF

nf :: Red TT
nf = red NF

redDef :: Form -> Red Def
redDef form ctx (Def n r ty body cs) = Def n r <$> red form ctx ty <*> redBody form ctx body <*> pure cs

redBody :: Form -> Red Body
redBody form ctx (Abstract a) = pure $ Abstract a
redBody form ctx (Term tm)    = Term <$> red form ctx tm
redBody NF   ctx (Clauses cs) = Clauses <$> traverse (redClause NF ctx) cs
redBody WHNF ctx body@(Clauses cs) = pure $ body

redClause :: Form -> Red Clause
redClause NF ctx (Clause pvs lhs rhs) =
    Clause
        <$> traverse (redDef NF ctx) pvs
        <*> redPat NF ctx lhs
        <*> red NF ctx rhs
redClause _ ctx clause = error $ "redClause non-NF"

redPat :: Form -> Red Pat
redPat NF ctx (PApp r f x) = PApp r <$> redPat NF ctx f <*> redPat NF ctx x
redPat NF ctx tm@(PV _)    = pure tm
redPat NF ctx (PForced tm) = PForced <$> red NF ctx tm
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

red :: Form -> Red TT

red form ctx t@(V Blank) = pure t

red form ctx t@(V n)
    | Just (Def _n r ty body cs) <- M.lookup n ctx
    = case body of
        Abstract _  -> pure t
        Term     tm -> red form ctx tm
        Clauses [Clause [] (PForced _) rhs] -> red form ctx rhs  -- constant function
        Clauses  cs -> pure t

    | otherwise = error $ "unknown variable: " ++ show n  -- unknown variable

red form ctx t
    | ("REDUCING", form, t, M.keys ctx) `dbg` False
    = undefined

red form ctx t@(I n i) = red form ctx (V n)

-- empty let binding
red form ctx t@(Bind Let [] tm) = red form ctx tm
red form ctx t@(Bind Let ds tm) = do
    reducedTm <- red form (insertDefs ds ctx) tm
    if reducedTm /= tm
        -- some progress: try again
        then red form ctx (Bind Let ds $ reducedTm)
        -- no progress: stop trying and go back
        else pure . simplLet . pruneLet . Bind Let ds $ reducedTm

-- The remaining binders are Pi and Lam.
red WHNF ctx t@(Bind b ds tm) = pure t  -- this is in WHNF already
red  NF  ctx t@(Bind b [] tm) = Bind b [] <$> red NF ctx tm
red  NF  ctx t@(Bind b (d:ds) tm)
    = do
        Bind _b ds' tm' <- red NF (M.insert (defName d) d ctx) $ Bind b ds tm
        d' <- redDef NF ctx d
        pure $ Bind b (d' : ds') tm'

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

red form ctx t@(App r f x) = do
    redF <- red form ctx f
    case redF of
        -- simple lambda
        Bind Lam (Def n' r' ty' (Abstract Var) cs : ds) tm'
          -> do
                rx <- redX
                tm'' <- red form ctx $ subst n' rx tm'
                pure $ case ds of
                    [] -> tm''
                    _  -> Bind Lam ds tm''

        _   -- pattern matching instance reduces as variable
            | (I fn _, args) <- unApply t
            -> red form ctx $ mkApp (V fn) args

            -- pattern-matching definitions
            | (V fn, args) <- unApply t
            , Just (defBody -> Clauses cs) <- M.lookup fn ctx
            -> do
                fm <- firstMatch <$> traverse (matchClause ctx fn t) cs
                case fm of
                    Yes rhs -> red form ctx rhs
                    _       -> App r redF <$> redX

            -- everything else
            | otherwise
            -> App r redF <$> redX  -- not a redex
  where
    redX = case form of
        NF   -> red NF ctx x
        WHNF -> pure x

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

matchClause :: IsRelevance r => Ctx r -> Name -> TT r -> Clause r -> Match (RM r (TT r))
matchClause ctx fn tm (Clause pvs lhs rhs) = do
    -- check that the matched term is actually an invocation of the given function
    () <- case tmH of
        V fn' | fn' == fn
            -> Yes ()
        _
            -> error $ "matchClause: function name mismatch: " ++ show (fn, tmH)

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

-- this function expects the term in any form, even unreduced
match :: IsRelevance r => Ctx r -> Ctx r -> Pat r -> TT r -> Match (RM r (M.Map Name (TT r)))
match pvs ctx (PV Blank) tm'
    = pure $ Yes M.empty

match pvs ctx (PForced tm) tm'
    = pure $ Yes M.empty

match pvs ctx (PV n) tm'
    | Just (defBody -> Abstract Var) <- M.lookup n pvs
    = pure . Yes $ M.singleton n tm'

match pvs ctx pat tm = matchWHNF pvs ctx pat =<< red WHNF ctx tm

equate :: IsRelevance r => r -> r -> RM r ()
equate r1 r2 = tell . CM $ r1 <-> r2

-- this function expects the term in WHNF
matchWHNF :: IsRelevance r => Ctx r -> Ctx r -> Pat r -> TT r -> Match (RM r (M.Map Name (TT r)))
matchWHNF pvs ctx (PV n) (V n')
    | n == n'
    , Just (defBody -> Abstract Constructor) <- M.lookup n ctx
    = pure $ Yes M.empty

matchWHNF pvs ctx (PApp r (PForced tm) x) (App r' f' x') = do
    tmR <- red WHNF ctx tm

    case unApply tmR of
        (V n,_)
            | n /= Blank
            , (defBody <$> M.lookup n ctx) /= Just (Abstract Constructor)
            -> error "forced pattern not constructor-headed"

            | Just (defBody -> Abstract Constructor) <- M.lookup n ctx
            -> match pvs ctx x x'  -- LHSs of the applications are constructor-headed

        _ -> Stuck

matchWHNF pvs ctx (PApp r f x) (App r' f' x')
    = M.unionWith (\_ _ -> error "non-linear pattern")
        <$> match pvs ctx f f'
        <*> match pvs ctx x x'

matchWHNF pvs ctx pat (V n)
    | Just d <- M.lookup n ctx
    = case defBody d of
        Abstract Var -> Stuck  -- variables may or may not match as we learn what they are
        Abstract (Foreign _) -> Stuck  -- foreigns are variables, really
        Abstract Postulate -> Stuck    -- postulates too
        _ -> No

matchWHNF _ _ _ _ = No

firstMatch :: Alternative f => [f a] -> f a
firstMatch = foldr (<|>) empty
