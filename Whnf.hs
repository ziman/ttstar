module Whnf (whnf) where

import TT
import qualified Data.Map as M

whnf :: Ctx r cs -> TT r -> TT r
whnf ctx t@(V n)
    | Just (Def _n r ty mtm cs) <- M.lookup n ctx
    = case mtm of
        Nothing -> t
        Just tm -> whnf ctx tm

    | otherwise = t  -- unknown variable

whnf ctx t@(Bind b n r ty tm) = t
whnf ctx t@(App pi_r r f x)
    | Bind Lam n' r' ty' tm' <- redF
    = whnf ctx $ subst n' x tm'

    | otherwise = t  -- not a redex
  where
    redF = whnf ctx f

whnf ctx t@(Case s alts) = redCase ctx t (whnf ctx s) alts
whnf ctx t@Erased = t
whnf ctx t@Type   = t

redCase :: Ctx r cs -> TT r -> TT r -> [Alt r] -> TT r
redCase ctx fallback _ (DefaultCase tm : _) = whnf ctx tm
redCase ctx fallback s (ConCase cn tm : as)
    | (V scn, sargs) <- unApply s
    , scn == cn  -- it's the same constructor
    = whnf ctx $ replaceCore (fromPat Lam tm) s
  where
    replaceCore :: TT r -> TT r -> TT r
    replaceCore newCore (App pi_r r f x) = App pi_r r (replaceCore newCore f) x
    replaceCore newCore _ = newCore

redCase ctx fallback s (_ : as) = redCase ctx fallback s as
redCase ctx fallback s [] = fallback
