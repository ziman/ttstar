{-# LANGUAGE KindSignatures, FlexibleContexts #-}
module TT.Utils where

import TT.Core

import Control.Monad
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

unApplyPat :: Pat r -> (Pat r, [(r, Pat r)])
unApplyPat pat = ua pat []
  where
    ua (PApp r f x) args = ua f ((r, x):args)
    ua pat args = (pat, args)

mkAppPat :: Pat r -> [(r, Pat r)] -> Pat r
mkAppPat f [] = f
mkAppPat f ((r, x) : xs) = mkAppPat (PApp r f x) xs

class Termy f where
    subst :: Name -> TT r -> f r -> f r
    freeVars :: f r -> S.Set Name

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

    freeVars (V n) = S.singleton n
    freeVars (I n ty) = S.insert n $ freeVars ty
    freeVars (Bind b ds tm) = freeVarsBinder ds tm
    freeVars (App r f x) = freeVars f `S.union` freeVars x

instance Termy Pat where
    subst n tm pat@(PV n')
        | n' == n   = error $ "trying to substitute for patvar: " ++ show n
        | otherwise = pat

    subst n tm pat@(PApp r f x)
        = PApp r (subst n tm f) (subst n tm x)

    subst n tm pat@(PForced tm')
        = PForced $ subst n tm tm'

    freeVars (PV n) = S.singleton n
    freeVars (PApp r f x) = freeVars f `S.union` freeVars x
    freeVars (PForced tm) = freeVars tm

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
    subst n tm (Clauses cs)  = Clauses $ map (subst n tm) cs

    freeVars (Abstract _)  = S.empty
    freeVars (Term tm)     = freeVars tm
    freeVars (Clauses cs)  = S.unions $ map freeVars cs

instance Termy Clause where
    subst n tm c@(Clause pvs lhs rhs)
        | n `elem` map defName pvs = c
        | otherwise = Clause (map (subst n tm) pvs) (subst n tm lhs) (subst n tm rhs)

    freeVars (Clause pvs lhs rhs)
        = (freeVars lhs `S.union` freeVars rhs)
            `S.difference` S.fromList (map defName pvs)

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

occursIn :: Termy a => Name -> a r -> Bool
n `occursIn` tm = n `S.member` freeVars tm

insertDefs :: [Def r] -> Ctx r -> Ctx r
insertDefs (d:ds) = insertDefs ds . M.insert (defName d) d
insertDefs []     = id

freePatVars :: Ctx r -> Pat r -> Maybe (S.Set Name)
freePatVars ctx (PV n)
    | Just (Def _n _r _ty (Abstract Constructor) _cs) <- M.lookup n ctx
    = Just S.empty

    | otherwise = Just $ S.singleton n
freePatVars ctx (PForced tm) = Just S.empty
freePatVars ctx (PApp r f x)
    = join (linUnion <$> freePatVars ctx f <*> freePatVars ctx x)
  where
    linUnion x y
        | S.null (S.intersection x y) = Just $ S.union x y
        | otherwise = Nothing

rename :: Termy a => Name -> Name -> a r -> a r
rename fromN toN = subst fromN (V toN)

-- TODO: order of subst? should it be foldl or foldr?
-- subst [(x, S y), (y, S x)] (x, y) = ?
-- * foldl: (S (S x), S x)
-- * foldr: (S y, S (S y))
substs :: Termy a => [(Name, TT r)] -> a r -> a r
substs ss x = foldl (\x (n, tm) -> subst n tm x) x ss

pat2term :: Pat r -> TT r
pat2term (PV n) = V n
pat2term (PApp r f x) = App r (pat2term f) (pat2term x)
pat2term (PForced tm) = tm

monomorphise :: TT r -> TT r
monomorphise (V n) = V n
monomorphise (I n ty) = V n
monomorphise (App r f x) = App r (monomorphise f) (monomorphise x)
monomorphise (Bind b d tm) = Bind b (map monoDef d) $ monomorphise tm
  where
    monoDef :: Def r -> Def r
    monoDef (Def n r ty b cs) = Def n r (monomorphise ty) (monoBody b) cs

    monoBody :: Body r -> Body r
    monoBody (Abstract a) = Abstract a
    monoBody (Term tm) = Term (monomorphise tm)
    monoBody (Clauses cs) = Clauses $ map monoClause cs

    monoClause :: Clause r -> Clause r
    monoClause (Clause pvs lhs rhs) = Clause (map monoDef pvs) (monoPat lhs) (monomorphise rhs)

    monoPat :: Pat r -> Pat r
    monoPat (PV n) = PV n
    monoPat (PForced tm) = PForced $ monomorphise tm
    monoPat (PApp r f x) = PApp r (monoPat f) (monoPat x)
