{-# LANGUAGE ViewPatterns #-}
module Optimisation.Identity (optimise) where

import TT.Core
import TT.Utils
import TT.Pretty ()

import qualified Data.Set as S

idTT :: TT ()
idTT = Bind Lam [Def (UN "x") () (V Blank) (Abstract Var) noConstrs] (V (UN "x"))

isIdClause :: S.Set Name -> Clause () -> Bool
isIdClause ids (Clause pvs [(_, PV arg)] rhs)
    = rmId ids rhs == PV arg
isIdClause ids (Clause [] [] rhs) = isIdTm ids rhs
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
rmIdPat ids (PV n) = PV n
rmIdPat ids (PCtor f cn args) = PCtor f cn [(r, rmIdPat ids p) | (r,p) <- args]
rmIdPat ids (PForced tm) = PForced $ rmId ids tm

rmIdClause :: S.Set Name -> Clause () -> Clause ()
rmIdClause ids (Clause pvs lhs rhs) = Clause pvs (rmIdPat ids lhs) (rmId ids rhs)
    -- we don't touch pvs because they don't contain anything interesting at this stage

rmIdBody :: S.Set Name -> Body () -> Body ()
rmIdBody ids (Term tm) = Term $ rmId ids tm
rmIdBody ids (Clauses cs) = Clauses $ map (rmIdClause ids) cs
rmIdBody ids b = b

rmIdDef :: S.Set Name -> Def () -> Def ()
rmIdDef ids (Def n () ty body _noConstrs) = Def n () ty (rmIdBody ids body) noConstrs

rmLet :: S.Set Name -> [Def ()] -> TT () -> TT ()
rmLet ids [] rhs = rmId ids rhs
rmLet ids (d:ds) rhs
    | isIdentity (S.insert (defName d) ids) d
    = rmLet (S.insert (defName d) ids) ds rhs

    | otherwise
    = let d' = rmIdDef ids d
        -- S.delete in case there's a conflicting identity in the enclosing scope
        in case rmLet (S.delete (defName d) ids) ds rhs of
            Bind Let ds' rhs' -> Bind Let (d':ds') rhs'
            rhs' -> Bind Let [d'] rhs'

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
rmId ids (Bind Let ds rhs) = rmLet ids ds rhs
rmId ids (Bind b ds rhs) = Bind b ds $ rmId ids rhs

optimise :: TT () -> TT ()
optimise = rmId S.empty
