module Codegen.Pretty where

import Codegen.IR
import Util.PrettyPrint

instance Show IR where show = prettyShow
instance Show IName where show = prettyShow
instance Show IBody where show = prettyShow
instance Show ICaseTree where show = prettyShow
instance Show IAlt where show = prettyShow

instance Pretty IName where
    pretty (IUN n) = text n

instance Pretty IR where
    pretty (IV n) = pretty n
    pretty (ILam n rhs) = text "\\" <> pretty n <> text "." <+> pretty rhs
    pretty (ILet n body rhs)
        = text "let" <+> pretty n <+> text "=" <+> pretty body
            $$ indent (text "in" <+> pretty rhs)
    pretty (IApp f x) = parens (pretty f <+> pretty x)
    pretty (IError s) = text "error" <+> text (show s)

instance Pretty IBody where
    pretty (IForeign code) = text "foreign" <+> text (show code)
    pretty (IConstructor arity) = text "constructor" <+> text (show arity)
    pretty (ICaseFun [] (ILeaf tm)) = pretty tm
    pretty (ICaseFun pvs ct)
        = hsep [text "\\" <> pv v <> text "." | v <- pvs]
            $$ indent (pretty ct)

instance Pretty ICaseTree where
    pretty (ILeaf tm) = pretty tm
    pretty (ICase v alts)
        = text "case" <+> pv v <+> text "of"
            $$ indent (vcat . map pretty $ alts)

instance Pretty IAlt where
    pretty (ICtor cn pvs ct)
        = pretty cn <+> hsep [pv v | v <- pvs]
            <+> text "=>" <+> pretty ct
    pretty (IDefault ct)
        = text "_" <+> text "=>" <+> pretty ct

pv :: Int -> Doc
pv i = text "_pv" <> int i

indent :: Doc -> Doc
indent = nest 2
