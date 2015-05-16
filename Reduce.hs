module Reduce where

import TTstar
import qualified Data.Map as M

type Ctx' r = M.Map Name (r, TT' r, Maybe (TT' r))

reduce :: Ctx' r -> TT' r -> TT' r
reduce ctx tm = tm

subst :: Name -> TT' r -> TT' r -> TT' r
subst n tm t@(V n')
    | n' == n   = tm
    | otherwise = t
subst n tm t@(Bind b r n' ty tm')
    | n' == n   = t
    | otherwise = Bind b r n' (subst n tm ty) (subst n tm tm')
subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)
subst _ _  t@(Prim _op) = t
subst n tm (Case s alts) = Case (subst n tm s) (map (substAlt n tm) alts)
subst _ _  t@(C _c) = t
subst _ _  t@Erased = t

substAlt :: Name -> TT' r -> Alt r -> Alt r
substAlt n tm (DefaultCase tm') = DefaultCase $ subst n tm tm'
substAlt n tm (ConstCase c tm') = ConstCase c $ subst n tm tm'
substAlt n tm t@(ConCase cn r ns tm')
    | n `elem` ns = t
    | otherwise   = ConCase cn r ns $ subst n tm tm'
