module TTUtils where

import TT
import TTLens

csDef :: Def r cs -> Def r cs'
csDef (Def n r ty body Nothing) = Def n r ty body Nothing

unApply :: TT r -> (TT r, [(r, TT r)])
unApply tm = ua tm []
  where
    ua (App r f x) args = ua f ((r, x) : args)
    ua tm args = (tm, args)

mkApp :: TT r -> [(r, TT r)] -> TT r
mkApp f [] = f
mkApp f ((r, x) : xs) = mkApp (App r f x) xs

class Termy a where
    subst :: Name -> TT r -> a -> a
    freeVars :: a -> S.Set Name

instance Termy (TT r) where
    subst n tm (V n')
        | n' == n   = tm
        | otherwise = V n'

    subst n tm (I n' ty) = I n' $ subst n tm ty

    subst n tm (Bind b d rhs)
        | n == boundName
        -- name bound here, substitute only in the type of d
        -- (the subst routine for Def will know it must not subst in the body of d)
        = Bind b (subst n tm d) rhs

        | boundName `occursIn` rhs
        -- we need to rename the binder
        = let
            d' = d{ defName = freshName, defBody = rename boundName freshName (defBody d) }
            rhs' = rename boundName freshName $ rhs
          in Bind b (subst n tm d') (subst n tm rhs')

        | otherwise  -- boring easy case
        = Bind b (subst n tm d) (subst n tm rhs)
    where
        boundName  = defName d
        freshName  = head [n | n <- nameSource, n `S.notMember` takenNames]
        takenNames = S.union (freeVars rhs) (freeVars . defBody $ d)
        nameSource = [UN (show n' ++ show i) | i <- [0..]]

    subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)

    freeVars (V n) = S.singleton n
    freeVars (I n ty) = S.insert n $ freeVars ty
    freeVars (Bind b d tm) = S.delete (defName d) (freeVars tm)
    freeVars (App r f x) = freeVars f `S.union` freeVars x

substCtx :: Name -> TT r -> Ctx r cs -> Ctx r cs
substCtx n tm = M.map $ substDef n tm

instance Termy (Def r cs) where
    subst n tm (Def dn r ty body mcs)
        | n == dn
        = Def dn r (subst n tm ty) body mcs  -- don't subst in body because those vars refer to `dn`

        | otherwise
        = Def dn r (subst n tm ty) (subst n tm body) mcs

    freeVars (Def dn r ty body mcs)
        = freeVars ty `S.union` S.delete dn (freeVars body)

instance Termy (Body r) where
    subst n tm (Abstract a)  = Abstract a
    subst n tm (Term t)      = Term $ subst n tm t
    subst n tm (Patterns cf) = Patterns $ subst n tm cf

    freeVars (Abstract _)  = S.empty
    freeVars (Term tm)     = freeVars tm
    freeVars (Patterns cf) = freeVars cf

instance Termy (CaseFun r) where
    subst n tm (CaseFun args ct)
        = error "TODO: this is tricky!"

    freeVars (CaseFun []     ct) = freeVars ct
    freeVars (CaseFun (d:ds) ct)
        = freeVars (defType d)
            `S.union`
                S.delete (defName d) (freeVars $ CaseFun ds ct)

instance Termy (CaseTree r) where
    subst n tm (Leaf t)
        = Leaf $ subst n tm t
    subst n tm (Case s alts)
        = Case (subst n tm s) $ map (subst n tm) alts

    freeVars (Leaf tm) = freeVars tm
    freeVars (Case s alts) = S.unions (freeVars s : map freeVars alts)

instance Termy (Alt r) where
    -- equations are pattern-only so they are not touched by substitution
    -- (but they must be rewritten if we rename the binders!)
    substAlt n tm (Alt Wildcard rhs) = Alt Wildcard $ substCaseTree n tm rhs
    substAlt n tm alt@(Alt lhs@(Ctor cn args eqs) rhs)
        = error "TODO: this is tricky!"

    freeVars (Alt Wildcard rhs) = freeVars rhs
    freeVars (Alt (Ctor cn [] eqs) rhs) = freeVars rhs
    freeVars (Alt (Ctor cn (d:ds) eqs) rhs)
        = freeVars (defType d)
            `S.union`
                S.delete (defName d) (freeVars $ Alt (Ctor cn ds eqs) rhs)

occursIn :: Termy a => Name -> a -> Bool
n `occursIn` tm = n `S.member` freeVars tm

rename :: Termy a => Name -> Name -> a -> a
rename fromN toN = subst fromN (V toN)

substLots :: (Name -> TT r -> a -> a) -> [(Name, TT r)] -> a -> a
substLots substF ss x = foldr (uncurry substF) x ss

substMany :: Show (Body r) => Ctx r cs -> TT r -> TT r
substMany ctx tm = foldl phi tm $ M.toList ctx
  where
    phi t (n, Def _ _ _ (Term tm) Nothing) = subst n tm t
    phi t (n, Def _ _ _ body Nothing)
        = error $ "trying to substMany something strange:\n  " ++ show n ++ " ~> " ++ show body
