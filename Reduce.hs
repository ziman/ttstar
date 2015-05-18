module Reduce where

import TT
import Pretty
import qualified Data.Map as M

type Ctx r = M.Map Name (r, TT r, Maybe (TT r))

reduce :: PrettyR r => Ctx r -> TT r -> TT r
reduce ctx t@(V n)
    | Just (r, ty, mtm) <- M.lookup n ctx
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

redCase :: PrettyR r => Ctx r -> TT r -> TT r -> [Alt r] -> TT r
redCase ctx t _ (DefaultCase tm : _) = reduce ctx tm
redCase ctx t s (ConCase cn r tm : as)
    | (V scn, sargs) <- unApply s
    , scn == cn  -- it's the same constructor
    = reduce ctx $ replaceCore (patToLam tm) s
  where
    replaceCore :: TT r -> TT r -> TT r
    replaceCore newCore (App r f x) = App r (replaceCore newCore f) x
    replaceCore newCore _ = newCore

    patToLam :: TT r -> TT r
    patToLam (Bind Pat r n ty tm) = Bind Lam r n ty $ patToLam tm
    patToLam tm = tm

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
