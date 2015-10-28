module Whnf (Form(..), red, whnf, nf) where

import TT
import qualified Data.Map as M

data Form = NF | WHNF

whnf :: Ctx r cs -> TT r -> TT r
whnf = red WHNF

nf :: Ctx r cs -> TT r -> TT r
nf = red NF

red :: Form -> Ctx r cs -> TT r -> TT r
red form ctx t@(V n)
    | Just (Def _n r ty mtm cs) <- M.lookup n ctx
    = case mtm of
        Nothing -> t
        Just tm -> red form ctx tm

    | otherwise = t  -- unknown variable

red WHNF ctx t@(Bind b n r ty rr tm) = t
red  NF  ctx t@(Bind b n r ty rr tm) = Bind b n r (red NF ctx ty) rr (red NF ctx' tm)
  where
    ctx' = M.insert n (Def n r ty Nothing Nothing) ctx

red WHNF ctx t@(App pi_r r f x)
    | Bind Lam n' r' ty' rr' tm' <- redF
    = red WHNF ctx $ subst n' x tm'

    | otherwise = t  -- not a redex
  where
    redF = red WHNF ctx f

red NF ctx t@(App pi_r r f x)
    | Bind Lam n' r' ty' rr' tm' <- redF
    = red NF ctx $ subst n' redX tm'

    | otherwise = App pi_r r redF redX  -- not a redex
  where
    redF = red NF ctx f
    redX = red NF ctx x

red form ctx t@(Let (Def n r ty mtm Nothing) tm)
    = red form (M.insert n (Def n r ty mtm Nothing) ctx) tm

red form ctx t@(Case s alts) = redCase form ctx t (red form ctx s) alts
red form ctx t@Erased = t
red form ctx t@Type   = t

redCase :: Form -> Ctx r cs -> TT r -> TT r -> [Alt r] -> TT r
redCase form ctx fallback _ (DefaultCase tm : _) = red form ctx tm
redCase form ctx fallback s (ConCase cn tm : as)
    | (V scn, sargs) <- unApply s
    , scn == cn  -- it's the same constructor
    = red form ctx $ replaceCore (fromPat Lam tm) s
  where
    replaceCore :: TT r -> TT r -> TT r
    replaceCore newCore (App pi_r r f x) = App pi_r r (replaceCore newCore f) x
    replaceCore newCore _ = newCore

redCase form ctx fallback s (_ : as) = redCase form ctx fallback s as
redCase form ctx fallback s [] = fallback
