module Codegen.SchemeIR (codegen) where

import Codegen.IR
import Util.PrettyPrint

indent :: Doc -> Doc
indent = nest 2

codegen :: IR -> Doc
codegen = cgTm

pv :: Int -> Doc
pv i = text "_pv" <> int i

cgTm :: IR -> Doc
cgTm (IV n) = cgName n
cgTm (ILam n rhs) = cgLambda n $ cgTm rhs
cgTm (ILet n body rhs) = cgLet n (cgBody n body) $ cgTm rhs
cgTm (IApp f x) = cgApp (cgTm f) (cgTm x)
cgTm (IError s) = cgApp (text "error") (text $ show s)

cgBody :: IName -> IBody -> Doc
cgBody n (IConstructor arity) = cgCtor n arity
cgBody n (IForeign code) = text code
cgBody n (ICaseFun pvs ct) = nestLambdas (map pv pvs) $ cgCaseTree ct

cgCaseTree :: ICaseTree -> Doc
cgCaseTree (ILeaf tm) = cgTm tm
cgCaseTree (ICase v alts) = cgCase (pv v) (map cgAlt alts)

cgAlt :: IAlt -> Doc
cgAlt (IDefault rhs) = parens (text "else" <+> cgCaseTree rhs)
cgAlt (ICtor cn pvs rhs) = parens (parens(text "'" <> cgName cn) <+> cgCaseTree rhs)

cgCase :: Doc -> [Doc] -> Doc
cgCase scrut alts = parens (text "case" <+> scrut $$ indent (vcat alts))

cgCtor :: IName -> Int -> Doc
cgCtor n arity
    = nestLambdas argNs $
        text"`" <> parens (
            cgName n
            <+> hsep [text "," <> n | n <- argNs]
        )
  where
    argNs = [text "e" <> int i | i <- [0..arity-1]]

nestLambdas :: [Doc] -> Doc -> Doc
nestLambdas [] = id
nestLambdas (n:ns) = cgLambda (IUN $ show n) . nestLambdas ns

cgApp :: Doc -> Doc -> Doc
cgApp f x = parens (f <+> x)

cgName :: IName -> Doc
cgName (IUN n) = text n

cgLambda :: IName -> Doc -> Doc
cgLambda n body = parens (text "lambda" <+> parens (cgName n) $+$ indent body)

cgLet :: IName -> Doc -> Doc -> Doc
cgLet n body rhs = parens (
        text "letrec" <+> parens (
            parens (cgName n <+> body)
        )
        $+$ indent rhs
    )
