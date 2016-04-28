module Normalise (Form(..), red, whnf, nf) where

import TT
import Pretty

import Control.Monad
import qualified Data.Map as M

import Debug.Trace

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
redBody form ctx (Clauses cls) = Clauses $ map (redClause form ctx) cls

redClause :: IsRelevance r => Form -> Ctx r cs -> Clause r -> Clause r
redClause WHNF ctx clause = clause
redClause NF ctx (Clause pvs lhs rhs)
    = Clause
        (map (redDef NF ctx) pvs)
        (red NF ctx lhs)
        (red NF ctx rhs)

red :: IsRelevance r => Form -> Ctx r cs -> TT r -> TT r
red form ctx t
    | ("REDUCING", form, t, M.keys ctx) `dbg` False
    = undefined

red form ctx t@(V n)
    | Just (Def _n r ty body cs) <- M.lookup n ctx
    = case body of
        Abstract _   -> t
        Term     tm  -> red form ctx tm
        Clauses  cls -> redClauses form ctx cls t

    | otherwise = error $ "unknown variable: " ++ show n  -- unknown variable

red form ctx t@(I n i) = red form ctx (V n)

red form ctx t@(Bind Let (Def n r ty body Nothing) tm)
    = red form (M.insert n (Def n r ty body Nothing) ctx) tm

red WHNF ctx t@(Bind b d tm) = t
red  NF  ctx t@(Bind b d tm) = Bind b (redDef NF ctx d) (red NF ctx' tm)
  where
    Def n r ty body Nothing = d
    ctx' = M.insert n (Def n r ty body Nothing) ctx

red form ctx t@(App r f x)
    | (V fn, args) <- unApply t
    , Just (Def _ _ _ (Clauses cls) _) <- M.lookup fn ctx
    = redClauses form ctx cls t

red WHNF ctx t@(App r f x)
    -- TODO: look up name in context, reduce clauses
    | Bind Lam (Def n' r' ty' (Abstract Var) Nothing) tm' <- redF
    = red WHNF ctx $ subst n' x tm'

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

red form ctx (Forced tm) = Forced $ red form ctx tm
red form ctx t@Erased = t
red form ctx t@Type   = t

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
    = let result = redClause' form ctx c tm
        in case ("RED-CLAUSE", c, tm, result) `dbg` result of
            Yep tm'  -> tm'
            Nope    -> redClauses form ctx cs tm
            Unknown -> tm

redClause' :: IsRelevance r => Form -> Ctx r cs -> Clause r -> TT r -> Tri (TT r)
redClause' form ctx (Clause pvs lhs rhs) tm
    | tmDepth < patDepth = Unknown  -- undersaturated

    | otherwise = do
        patSubst <- match form patVars [lhs] [tm']
        let patValues = foldr (M.insert <$> defName <*> id) ctx patSubst
        if M.keysSet patVars /= M.keysSet patValues
            then error "not all pattern vars bound in match"
            else return ()
        return . red form patValues $ rewrap rhs extra
  where
    patDepth = appDepth lhs
    tmDepth = appDepth tm
    (tm', extra) = unwrap (tmDepth - patDepth) tm
    patVars = foldr (M.insert <$> defName <*> csDef) ctx pvs

match :: IsRelevance r => Form -> Ctx r cs -> [TT r] -> [TT r] -> Tri (Ctx r cs)
match form ctx ls rs
    = M.unions <$> zipWithM (matchTm form ctx) ls rs

matchTm :: IsRelevance r => Form -> Ctx r cs -> TT r -> TT r -> Tri (Ctx r cs)
matchTm form ctx pat tm
    | ("MATCH", pat, tm) `dbg` False
    = undefined

-- patvars match anything
matchTm form ctx (V n) tm
    | Just d@(Def n r ty (Abstract Var) Nothing) <- M.lookup n ctx
    = Yep $ M.singleton n (Def n r ty (Term tm) Nothing)

-- data constructors match
matchTm form ctx pattern@(App _ _ _) tm@(App _ _ _)
    | (V cn , args ) <- unApply pattern
    , (V cn', args') <- unApply tm
    , cn == cn'  -- heads are the same
--    , Just (Def _ _ _ (Abstract Postulate) Nothing) <- M.lookup cn ctx  -- is a ctor/postulate
    = match form ctx (map (red form ctx) args) (map (red form ctx) args')

-- forced patterns always match, not generating anything
matchTm form ctx (Forced _) tm
    = Yep M.empty

-- equal terms match
matchTm form ctx tm tm'
    | tm == tm'
    = Yep M.empty

matchTm form ctx _ _ = Nope
