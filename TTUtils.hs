{-# LANGUAGE KindSignatures, FlexibleContexts #-}
module TTUtils where

import TT

import qualified Data.Map as M
import qualified Data.Set as S

unApply :: TT r -> (TT r, [(r, TT r)])
unApply tm = ua tm []
  where
    ua (App r f x) args = ua f ((r, x) : args)
    ua tm args = (tm, args)

mkApp :: TT r -> [(r, TT r)] -> TT r
mkApp f [] = f
mkApp f ((r, x) : xs) = mkApp (App r f x) xs

class Termy f where
    subst :: Name -> TT r -> f r -> f r
    freeVars :: f r -> S.Set Name

{-
instance Termy Ctx where
    subst n tm ctx
        = M.fromList [(n', subst n tm d) | (n', d) <- M.toList ctx, n' /= n]

    freeVars ctx
        = S.unions (map freeVars $ M.elems ctx) `S.difference` M.keysSet ctx
-}

instance Termy TT where
    subst n tm (V n')
        | n' == n   = tm
        | otherwise = V n'

    subst n tm (I n' ty)
        | n' == n   = tm
        | otherwise = I n' $ subst n tm ty

    subst n tm (Bind b ds rhs) = Bind b ds' rhs'
      where
        (ds', rhs') = substBinder n tm ds rhs

    subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)

    subst n tm (Forced t) = Forced (subst n tm t)

    freeVars (V n) = S.singleton n
    freeVars (I n ty) = S.insert n $ freeVars ty
    freeVars (Bind b ds tm) = freeVarsBinder ds tm
    freeVars (App r f x) = freeVars f `S.union` freeVars x
    freeVars (Forced tm) = freeVars tm

instance Termy Def where
    subst n tm (Def dn r ty body mcs)
        | n == dn
        = Def dn r (subst n tm ty) body mcs  -- don't subst in body because those vars refer to `dn`

        | otherwise
        = Def dn r (subst n tm ty) (subst n tm body) mcs

    freeVars (Def dn r ty body mcs)
        = freeVars ty `S.union` S.delete dn (freeVars body)

instance Termy Body where
    subst n tm (Abstract a)  = Abstract a
    subst n tm (Term t)      = Term $ subst n tm t
    subst n tm (Patterns cf) = Patterns $ subst n tm cf

    freeVars (Abstract _)  = S.empty
    freeVars (Term tm)     = freeVars tm
    freeVars (Patterns cf) = freeVars cf

instance Termy CaseFun where
    -- see (subst n tm (Bind b d rhs)) for the general approach to subst under binders
    subst n tm (CaseFun ds ct) = CaseFun ds' ct'
      where
        (ds', ct') = substBinder n tm ds ct

    freeVars (CaseFun ds ct) = freeVarsBinder ds ct

freeVarsBinder :: Termy a => [Def r] -> a r -> S.Set Name
freeVarsBinder [] rhs = freeVars rhs
freeVarsBinder (d:ds) rhs
    = freeVars (defType d)
        `S.union`
            S.delete (defName d)
                (freeVars (defBody d)
                    `S.union`
                        freeVarsBinder ds rhs
                )

substBinder :: Termy a
    => Name -> TT r
    ->  [Def r] -> a r
    -> ([Def r],   a r)
substBinder n tm [] rhs = ([], subst n tm rhs)
substBinder n tm (d:ds) rhs
    | n == boundName
    -- Name bound here, substitute only in the type of d.
    -- (The subst routine for Def will know not to subst in the body of d.)
    = (subst n tm d : ds, rhs)

    | boundName `occursIn` tm
    -- we need to rename the binder
    = let
        -- just a call to `freshen` won't work here because we're renaming the name of the def
        d'   = d{ defName = freshName, defBody = freshen (defBody d) }
        -- now we can perform the substitution we want
        (ds', rhs') = substBinder n tm (map freshen ds) (freshen rhs)
      in 
        (subst n tm d' : ds', rhs')

    | otherwise  -- boring easy case, we just plug it in
    = let
        (ds', rhs') = substBinder n tm ds rhs
      in 
        (subst n tm d : ds', rhs')
  where
    boundName  = defName d
    freshName  = head [n | n <- nameSource, n `S.notMember` takenNames]
    takenNames = freeVars rhs `S.union` (freeVars . defBody $ d)
    nameSource = [UN (show boundName ++ show i) | i <- [0 :: Integer ..]]

    freshen :: Termy a => a r -> a r
    freshen = rename boundName freshName

instance Termy CaseTree where
    subst n tm (Leaf t)
        = Leaf $ subst n tm t
    subst n tm (Case r s alts)
        = Case r (subst n tm s) $ map (subst n tm) alts

    freeVars (Leaf tm) = freeVars tm
    freeVars (Case r s alts) = S.unions (freeVars s : map freeVars alts)

instance Termy Alt where
    -- equations are pattern-only so they are not touched by substitution
    -- (but they must be rewritten if we rename the binders!)
    subst n tm (Alt Wildcard rhs) = Alt Wildcard $ subst n tm rhs

    subst n tm (Alt (Ctor ct args) rhs)
        = Alt (Ctor ct args') rhs'
      where
        (args', rhs') = substBinder n tm args rhs

    subst n tm (Alt (ForcedPat ftm) rhs)
        = Alt (ForcedPat $ subst n tm ftm) (subst n tm rhs)

    freeVars (Alt Wildcard rhs) = freeVars rhs
    freeVars (Alt (Ctor ct args) rhs)
        = freeVarsBinder args rhs
    freeVars (Alt (ForcedPat ftm) rhs)
        = freeVars ftm `S.union` freeVars rhs

occursIn :: Termy a => Name -> a r -> Bool
n `occursIn` tm = n `S.member` freeVars tm

insertDefs :: [Def r] -> Ctx r -> Ctx r
insertDefs (d:ds) = insertDefs ds . M.insert (defName d) d
insertDefs []     = id

rename :: Termy a => Name -> Name -> a r -> a r
rename fromN toN = subst fromN (V toN)

-- TODO: order of subst? should it be foldl or foldr?
-- subst [(x, S y), (y, S x)] (x, y) = ?
-- * foldl: (S (S x), S x)
-- * foldr: (S y, S (S y))
substs :: Termy a => [(Name, TT r)] -> a r -> a r
substs ss x = foldl (\x (n, tm) -> subst n tm x) x ss
