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

    subst n tm (Bind b d rhs) = Bind b d' rhs'
      where
        ([d'], rhs') = substBinder n tm [d] [] rhs

    subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)

    freeVars (V n) = S.singleton n
    freeVars (I n ty) = S.insert n $ freeVars ty
    freeVars (Bind b d tm) = freeVarsBinder [d] [] tm
    freeVars (App r f x) = freeVars f `S.union` freeVars x

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
    -- see (subst n tm (Bind b d rhs)) for the general approach to subst under binders
    subst n tm (CaseFun ds ct) = CaseFun ds' ct'
      where
        (ds', ct') = substBinder n tm d ct

    freeVars (CaseFun ds ct) = freeVarsBinder ds [] ct

instance Termy (Name, TT r) where
    subst n tm@(V n') (en, etm)
        | n == en
        = (n', subst n tm etm)

        | (en, subst n tm etm)

    subst n tm (en, etm)
        | n == en
        = error $ "trying to substitute something strange in eqs: " ++ show n ++ " ~> " ++ show tm

        | otherwise
        = (en, subst n tm etm)

    freeVars (en, etm) = S.insert en (freeVars etm)

-- eqs are lumped together with rhs, all the way under all defs,
-- which means we don't have to worry about them until we've reached the base case
freeVarsBinder :: Termy a => [Def r cs] -> [(Name, TT r)] -> a -> S.Set Name
freeVarsBinder [] eqs rhs = S.unions (freeVars rhs : map freeVars eqs)
freeVarsBinder (d:ds) eqs rhs
    = freeVars (defType d)
        `S.union`
            S.delete (defName d)
                (freeVars (defBody d)
                    `S.union`
                        freeVarsBinder ds eqs rhs
                )

substBinder :: Termy a => Name -> TT r -> [Def r cs] -> [(Name, TT r)] -> a -> ([Def r cs], [(Name, TT r)], a)
substBinder n tm [] eqs rhs = ([], map (subst n tm) eqs, subst n tm rhs)
substBinder n tm (d:ds) eqs rhs
    | n == boundName
    -- Name bound here, substitute only in the type of d.
    -- (The subst routine for Def will know not to subst in the body of d.)
    = (subst n tm d : ds, eqs, rhs)

    | boundName `occursIn` tm
    -- we need to rename the binder
    = let
        -- just a call to `freshen` won't work here because we're renaming the name of the def
        d'   = d{ defName = freshName, defBody = freshen (defBody d) }
        -- now we can perform the substitution we want
        (ds', eqs', rhs') = substBinder n tm (freshen ds) (map freshen eqs) (freshen rhs)
      in 
        (subst n tm d' : ds', eqs', rhs')

    | otherwise  -- boring easy case, we just plug it in
    = let
        (ds', eqs', rhs') = substBinder n tm ds rhs
      in 
        (subst n tm d : ds', eqs', rhs')
  where
    boundName  = defName d
    freshName  = head [n | n <- nameSource, n `S.notMember` takenNames]
    takenNames = S.unions (freeVars rhs : (freeVars . defBody $ d) : map freeVars eqs)
    nameSource = [UN (show boundName ++ show i) | i <- [0..]]

    freshen :: Termy a => a -> a
    freshen = rename boundName freshName

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
    substAlt n tm (Alt (Ctor cn args eqs) rhs)
        = Alt (Ctor cn args' eqs') rhs'
      where
        (args', eqs', rhs') = substBinder n tm args eqs rhs

    freeVars (Alt Wildcard rhs) = freeVars rhs
    freeVars (Alt (Ctor cn args eqs) rhs)
        = freeVarsBinder args eqs rhs

occursIn :: Termy a => Name -> a -> Bool
n `occursIn` tm = n `S.member` freeVars tm

rename :: Termy a => Name -> Name -> a -> a
rename fromN toN = subst fromN (V toN)

substs :: Termy a => [(Name, TT r)] -> a -> a
substs ss x = foldr (uncurry subst) x ss

substMany :: Show (Body r) => Ctx r cs -> TT r -> TT r
substMany ctx tm = foldl phi tm $ M.toList ctx
  where
    phi t (n, Def _ _ _ (Term tm) Nothing) = subst n tm t
    phi t (n, Def _ _ _ body Nothing)
        = error $ "trying to substMany something strange:\n  " ++ show n ++ " ~> " ++ show body
