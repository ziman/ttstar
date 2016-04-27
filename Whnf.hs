module Whnf (Form(..), red, whnf, nf) where

import TT
import qualified Data.Map as M

data Form = NF | WHNF

whnf :: Ctx r cs -> TT r -> TT r
whnf = red WHNF

nf :: Ctx r cs -> TT r -> TT r
nf = red NF

redDef :: Form -> Ctx r cs -> Def r cs' -> Def r cs'
redDef form ctx (Def n r ty body cs) = Def n r (red form ctx ty) (redBody form ctx body) cs

redBody :: Form -> Ctx r cs -> Body r -> Body r
redBody form ctx Abstract = Abstract
redBody form ctx (Term tm) = Term (red form ctx tm)
redBody form ctx (Clauses cls) = Clauses $ map (redClause form ctx) cls

redClause :: Form -> Ctx r cs -> Clause r -> Clause r
redClause WHNF ctx clause = clause
redClause NF ctx (Clause pvs lhs rhs)
    = Clause
        (map (redDef NF ctx) pvs)
        (red NF ctx lhs)
        (red NF ctx rhs)

red :: Form -> Ctx r cs -> TT r -> TT r
red form ctx t@(V n)
    | Just (Def _n r ty body cs) <- M.lookup n ctx
    = case body of
        Abstract -> t
        Term tm  -> red form ctx tm
        Clauses cls -> t

    | otherwise = t  -- unknown variable

red form ctx t@(I n i) = red form ctx (V n)

red WHNF ctx t@(Bind b d tm) = t
red  NF  ctx t@(Bind b d tm) = Bind b (redDef NF ctx d) (red NF ctx' tm)
  where
    Def n r ty body Nothing = d
    ctx' = M.insert n (Def n r ty body Nothing) ctx

red WHNF ctx t@(App r f x)
    -- TODO: look up name in context, reduce clauses
    | Bind Lam (Def n' r' ty' Abstract Nothing) tm' <- redF
    = red WHNF ctx $ subst n' x tm'

    | otherwise = t  -- not a redex
  where
    redF = red WHNF ctx f

red NF ctx t@(App r f x)
    | Bind Lam (Def n' r' ty' Abstract Nothing) tm' <- redF
    = red NF ctx $ subst n' redX tm'

    | otherwise = App r redF redX  -- not a redex
  where
    redF = red NF ctx f
    redX = red NF ctx x

red form ctx (Forced tm) = Forced $ red form ctx tm
red form ctx t@Erased = t
red form ctx t@Type   = t
