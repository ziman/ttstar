module Codegen.ToIR (irTm) where

import TT.Core
import TT.Pretty ()

import Codegen.IR

irName :: Name -> IName
irName n = IMN (show n) 0

irTm :: TT () -> IR
irTm (V n) = IV (irName n)
irTm (App () f x) = IApp (irTm f) (irTm x)
irTm (Bind Lam [Def n () _ty _body _cs] rhs) = ILam (irName n) (irTm rhs)
irTm (Bind Let [] rhs) = irTm rhs
irTm (Bind Let (Def n () ty body _cs : ds) rhs)
    = ILet (irName n) (irBody ty body) $ irTm (Bind Let ds rhs)
irTm tm = error $ "irTm: cannot translate: " ++ show tm

irBody :: TT () -> Body () -> IBody
irBody ty (Clauses cs) = ICaseTree $ compile cs
irBody ty (Term tm) = ICaseTree $ ILeaf (irTm tm)
irBody ty (Abstract Constructor) = IConstructor (length $ argNames ty)
irBody ty (Abstract Postulate) = ICaseTree $ ILeaf (IError "postulate")
irBody ty (Abstract (Foreign code)) = IForeign code
irBody ty b = error $ "irBody: cannot translate: " ++ show b

argNames :: TT () -> [Name]
argNames (Bind Pi ds rhs) = map defName ds ++ argNames rhs
argNames _ = []

compile :: [Clause ()] -> ICaseTree
compile clauses = error "not implemented"
