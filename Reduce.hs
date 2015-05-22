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

reduce ctx (Bind b r n ty tm) = Bind b r n (reduce ctx ty) (reduce ctx tm)
reduce ctx (App r f x)

    | Bind Lam r' n' ty' tm' <- redF
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

unApply :: TT r -> (TT r, [TT r])
unApply tm = ua tm []
  where
    ua (App _ f x) args = ua f (x : args)
    ua tm args = (tm, args)

subst :: Name -> TT r -> TT r -> TT r
subst n tm t@(V n')
    | n' == n   = tm
    | otherwise = t
subst n tm t@(Bind b r n' ty tm')
    | n' == n   = t
    | otherwise = Bind b r n' (subst n tm ty) (subst n tm tm')
subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)
subst n tm (Case s alts) = Case (subst n tm s) (map (substAlt n tm) alts)
subst _ _  t@Erased = t
subst _ _  t@Type   = t

substAlt :: Name -> TT r -> Alt r -> Alt r
substAlt n tm (DefaultCase tm') = DefaultCase $ subst n tm tm'
substAlt n tm t@(ConCase cn r tm') = ConCase cn r $ subst n tm tm'

-- split a Pat-packed pattern into 1. pattern vars, 2. RHS
splitBinder :: Binder -> TT r -> ([(Name, r, TT r)], TT r)
splitBinder bnd (Bind b r n ty tm)
    | b == bnd
    = ((n, r, ty) : args, rhs)
  where
    (args, rhs) = splitBinder bnd tm
splitBinder bnd tm = ([], tm)

fromPat :: Binder -> TT r -> TT r
fromPat b (Bind Pat r n ty tm) = Bind b r n ty $ fromPat b tm
fromPat b tm = tm
