{-# LANGUAGE ViewPatterns #-}
module Optimisation.Identity (optimise) where

import TT
import TTUtils
import Pretty ()

import qualified Data.Set as S

idTT :: TT ()
idTT = Bind Lam [Def (UN "x") () (V Blank) (Abstract Var) noConstrs] (V (UN "x"))

isIdClause :: S.Set Name -> Clause () -> Bool
isIdClause ids (Clause pvs (PApp _r _f arg) rhs)
    = rmId ids (pat2term arg) == rmId ids rhs
isIdClause ids (Clause [] (PForced _f) tm)
    = isIdTm ids tm
isIdClause _ _ = False

isIdTm' :: TT () -> Bool
isIdTm' (Bind Lam [Def n () _ _ _] (V n')) | n == n' = True
isIdTm' _ = False

isIdTm :: S.Set Name -> TT () -> Bool
isIdTm ids = isIdTm' . rmId ids

isIdentity :: S.Set Name -> Def () -> Bool
isIdentity ids (defBody -> Clauses cs) = all (isIdClause ids) cs
isIdentity ids (defBody -> Term tm) = isIdTm ids tm
isIdentity ids _ = False

rmIdPat :: S.Set Name -> Pat () -> Pat ()
rmIdPat ids (PApp () f x) = PApp () (rmIdPat ids f) (rmIdPat ids x)
rmIdPat ids (PForced tm) = PForced $ rmId ids tm
rmIdPat ids pat = pat

rmIdClause :: S.Set Name -> Clause () -> Clause ()
rmIdClause ids (Clause pvs lhs rhs) = Clause pvs (rmIdPat ids lhs) (rmId ids rhs)
    -- we don't touch pvs because they don't contain anything interesting at this stage

rmIdBody :: S.Set Name -> Body () -> Body ()
rmIdBody ids (Term tm) = Term $ rmId ids tm
rmIdBody ids (Clauses cs) = Clauses $ map (rmIdClause ids) cs
rmIdBody ids b = b

rmIdDef :: S.Set Name -> Def () -> Def ()
rmIdDef ids (Def n () ty body _noConstrs) = Def n () ty (rmIdBody ids body) noConstrs

rmBind :: S.Set Name -> Binder -> [Def ()] -> TT () -> TT ()
rmBind ids b [] rhs = rmId ids rhs
rmBind ids b (d:ds) rhs
    | isIdentity ids d = rmBind (S.insert (defName d) ids) b ds rhs
    | otherwise =
        let d' = rmIdDef ids d
          -- S.delete in case there's a conflicting identity in the enclosing scope
          in case rmBind (S.delete (defName d) ids) b ds rhs of
                Bind b' ds' rhs' | b' == b -> Bind b (d':ds') rhs'
                rhs' -> Bind b [d'] rhs'

rmId :: S.Set Name -> TT () -> TT ()
rmId ids tm@(V n)
    | n `S.member` ids = idTT
    | otherwise = tm

rmId ids (App () (V f) x)
    | f `S.member` ids = x'
    | otherwise = App () (V f) x'
  where
    x' = rmId ids x

rmId ids (App () f x) = App () (rmId ids f) (rmId ids x)
rmId ids tm@(I _ _) = error $ "rmId: instance found: " ++ show tm
rmId ids (Bind b ds rhs) = rmBind ids b ds rhs

optimise :: TT () -> TT ()
optimise = rmId S.empty
