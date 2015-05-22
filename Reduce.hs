module Reduce where

import TT
import qualified Data.Map as M

type Ctx r cs = M.Map Name (r, TT r, Maybe (TT r), cs)

reduce :: Ctx r cs -> TT r -> TT r
reduce ctx t@(V n)
    | Just (r, ty, mtm, cs) <- M.lookup n ctx
    = case mtm of
        Nothing -> t
        Just tm -> reduce ctx tm

    | otherwise = t  -- unknown variable

reduce ctx (Bind b n r ty tm) = Bind b n r (reduce ctx ty) (reduce ctx tm)
reduce ctx (App r f x)

    | Bind Lam n' r' ty' tm' <- redF
    = reduce ctx $ subst n' x tm'

    | otherwise = App r redF (reduce ctx x)
  where
    redF = reduce ctx f

reduce ctx t@(Case s alts) = redCase ctx t (reduce ctx s) alts
reduce ctx t@Erased = t
reduce ctx t@Type   = t

redCase :: Ctx r cs -> TT r -> TT r -> [Alt r] -> TT r
redCase ctx t _ (DefaultCase tm : _) = reduce ctx tm
redCase ctx t s (ConCase cn r tm : as)
    | (V scn, sargs) <- unApply s
    , scn == cn  -- it's the same constructor
    = reduce ctx $ replaceCore (fromPat Lam tm) s
  where
    replaceCore :: TT r -> TT r -> TT r
    replaceCore newCore (App r f x) = App r (replaceCore newCore f) x
    replaceCore newCore _ = newCore

redCase ctx t s (_ : as) = redCase ctx t s as
redCase ctx t s [] = t
