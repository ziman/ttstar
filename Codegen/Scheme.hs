module Codegen.Scheme (codegen) where

import TT
import Pretty ()
import Util.PrettyPrint
import Codegen.Common

indent :: Doc -> Doc
indent = nest 2

cgName :: Name -> Doc
cgName = text . show

cgTm :: TT () -> Doc
cgTm (V n) = cgName n
cgTm tm@(I n ty) = error $ "e-instance in codegen: " ++ show tm
cgTm (Bind Lam (Def n () ty (Abstract Var) cs) rhs) = cgLambda n $ cgTm rhs
cgTm (Bind Let (Def n () ty (Term tm) cs) rhs) = cgLet [(n, cgTm tm)] (cgTm rhs)
cgTm (App () f x) = cgApp (cgTm f) (cgTm x)
cgTm tm = error $ "can't cg tm: " ++ show tm

cgApp :: Doc -> Doc -> Doc
cgApp f x = parens (f <+> x)

cgDef :: Def () -> Doc
cgDef (Def n r ty (Abstract Postulate) cs)
    = cgDefine n . nestLambdas args $
        text "`" <> parens (
            cgName n <+> hsep [text "," <> cgName n | n <- args]
        )
  where
    args = [UN $ "e" ++ show i | i <- [0..nargs ty - 1]]

cgDef (Def n r ty (Patterns (CaseFun args ct)) cs) =
    cgDefine n . nestLambdas (map defName args)
        $ cgCase ct

cgDef (Def n r ty (Term tm) cs) = cgDefine n $ cgTm tm
cgDef d@(Def n r ty b cs) = error $ "can't cg def: " ++ show d

cgCase :: CaseTree () -> Doc
cgCase (Leaf tm) = cgTm tm
cgCase (Case () scrut alts) =
    cgLet [(UN "match-head", cgApp (text "car") (cgTm scrut))]
        (text "not-implemented")

cgDefine :: Name -> Doc -> Doc
cgDefine n body = parens (text "define" <+> cgName n $+$ indent body)

cgLambda :: Name -> Doc -> Doc
cgLambda n body = parens (text "lambda" <+> parens (cgName n) $+$ indent body)

cgLet :: [(Name, Doc)] -> Doc -> Doc
cgLet defs rhs = parens (
        text "let" <+> parens (
            hsep [parens (cgName n <+> body) | (n, body) <- defs]
        )
        $+$ indent rhs
    )

nestLambdas :: [Name] -> Doc -> Doc
nestLambdas [] = id
nestLambdas (n:ns) = cgLambda n . nestLambdas ns

nargs :: TT () -> Int
nargs (Bind Pi d rhs) = 1 + nargs rhs
nargs _ = 0

cgProgram :: Program () -> Doc
cgProgram (Prog defs) = vcat [
    cgDef def $+$ blankLine
    | def <- defs
    ] $+$ text "main"

codegen :: Codegen
codegen = Codegen
    { cgRun = cgProgram
    , cgExt = "scm"
    }
