module Codegen.Scheme (codegen) where

import TT
import Pretty ()
import Util.PrettyPrint
import Codegen.Common

cgName :: Name -> Doc
cgName = text . show

cgTm :: TT () -> Doc
cgTm tm = error $ "can't cg tm: " ++ show tm

cgDef :: Def () -> Doc
cgDef (Def n r ty (Abstract Postulate) cs) = empty
cgDef (Def n r ty (Term tm) cs)
    = parens (
        text "define" <+> cgName n <+> cgTm tm
    )
cgDef d@(Def n r ty b cs) = error $ "can't cg def: " ++ show d

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
