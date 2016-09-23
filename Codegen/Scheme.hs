module Codegen.Scheme (codegen) where

import TT
import Pretty ()
import Util.PrettyPrint
import Codegen.Common

cgName :: Name -> Doc
cgName = text . show

cgTm :: TT () -> Doc
cgTm (V n) = cgName n
cgTm tm@(I n ty) = error $ "e-instance in codegen: " ++ show tm
cgTm (Bind Lam (Def n () ty (Abstract Var) cs) rhs) = parens (
        text "lambda" <+> parens (cgName n) <+> cgTm rhs
    )
cgTm (Bind Let (Def n () ty (Term tm) cs) rhs) = parens (
        text "let" <+> parens (parens (
            cgName n <+> cgTm tm
        )) <+> cgTm rhs
    )
cgTm (App () f x) = parens (cgTm f <+> cgTm x)
cgTm tm = error $ "can't cg tm: " ++ show tm

cgDef :: Def () -> Doc
cgDef (Def n r ty (Abstract Postulate) cs)
    = parens (
        text "define" <+> cgName n
        <+> parens (
            text "lambda"
            <+> parens argList
            <+> text "`" <> parens (
                cgName n <+> argList
            )
        )
    )
  where
    argList = hsep $ map text args
    args = ["e" ++ show i | i <- [0..nargs ty - 1]]

cgDef (Def n r ty (Term tm) cs)
    = parens (
        text "define" <+> cgName n <+> cgTm tm
    )
cgDef d@(Def n r ty b cs) = error $ "can't cg def: " ++ show d

nargs :: TT () -> Int
nargs (Bind Pi d rhs) = 1 + nargs rhs
nargs _ = 0

cgProgram :: Program () -> Doc
cgProgram (Prog defs) = vcat [
    cgDef def $+$ blankLine
    | def <- defs
    ]

codegen :: Codegen
codegen = Codegen
    { cgRun = cgProgram
    , cgExt = "scm"
    }
