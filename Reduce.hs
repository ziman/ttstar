module Reduce where

import TTstar
import qualified Data.Map as M

type Ctx' r = M.Map Name (r, TT' r, Maybe (TT' r))

reduce :: ShowR r => Ctx' r -> TT' r -> TT' r
reduce ctx t@(V n)
    | Just (r, ty, mtm) <- M.lookup n ctx
    = case mtm of
        Nothing -> t
        Just tm -> reduce ctx tm

    | otherwise = error $ "unknown variable " ++ show n

reduce ctx (Bind b r n ty tm) = Bind b r n (reduce ctx ty) (reduce ctx tm)
reduce ctx (App r f x)
    | Bind Lam r' n' ty' tm' <- redF
    = reduce ctx $ subst n' x tm'

    | otherwise = App r redF (reduce ctx x)
  where
    redF = reduce ctx f

reduce ctx (Case s alts) = redCase ctx (reduce ctx s) alts
reduce ctx t@Erased = t
reduce ctx t@Type   = t

redCase :: ShowR r => Ctx' r -> TT' r -> [Alt r] -> TT' r
redCase ctx _ (DefaultCase tm : _) = reduce ctx tm
redCase ctx s (ConCase cn _r ns tm : as)
    | (V cn', args) <- unApply s
    , length args == length ns
    = reduce ctx $ subst' (zip ns args) tm
  where
    subst' ((n,x):xs) tm = subst' xs $ subst n x tm
    subst' [] tm = tm

redCase ctx s (_ : as) = redCase ctx s as
redCase ctx s [] = error $ "uncovered case: " ++ show s

unApply :: TT' r -> (TT' r, [TT' r])
unApply tm = ua tm []
  where
    ua (App _ f x) args = ua f (x : args)
    ua tm args = (tm, args)

subst :: Name -> TT' r -> TT' r -> TT' r
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

substAlt :: Name -> TT' r -> Alt r -> Alt r
substAlt n tm (DefaultCase tm') = DefaultCase $ subst n tm tm'
substAlt n tm t@(ConCase cn r ns tm')
    | n `elem` ns = t
    | otherwise   = ConCase cn r ns $ subst n tm tm'
