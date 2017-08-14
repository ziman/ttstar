module Codegen.ToIR (toIR) where

import TT.Core
import TT.Utils (unApplyPat)
import TT.Pretty ()

import Codegen.IR

import Data.List

toIR :: TT () -> IR
toIR = irTm 0

irName :: Name -> IName
irName n = IMN (show n) 0

irTm :: Int -> TT () -> IR
irTm pv (V n) = IV (irName n)
irTm pv (App () f x) = IApp (irTm pv f) (irTm pv x)
irTm pv (Bind Lam [Def n () _ty _body _cs] rhs) = ILam (irName n) (irTm pv rhs)
irTm pv (Bind Let [] rhs) = irTm pv rhs
irTm pv (Bind Let (Def n () ty body _cs : ds) rhs)
    = ILet (irName n) (irBody pv ty body) $ irTm pv (Bind Let ds rhs)
irTm pv tm = error $ "irTm: cannot translate: " ++ show tm

irBody :: Int -> TT () -> Body () -> IBody
irBody pv ty (Clauses cs) = ICaseTree $ compile pv cs
irBody pv ty (Term tm) = ICaseTree $ ILeaf (irTm pv tm)
irBody pv ty (Abstract Constructor) = IConstructor (length $ argNames ty)
irBody pv ty (Abstract Postulate) = ICaseTree $ ILeaf (IError "postulate")
irBody pv ty (Abstract (Foreign code)) = IForeign code
irBody pv ty b = error $ "irBody: cannot translate: " ++ show b

argNames :: TT () -> [Name]
argNames (Bind Pi ds rhs) = map defName ds ++ argNames rhs
argNames _ = []

compile :: Int -> [Clause ()] -> ICaseTree
compile pv clauses = error "not implemented"
  where
    columns = transpose [snd $ unApplyPat lhs | Clause pvs lhs rhs <- clauses]
