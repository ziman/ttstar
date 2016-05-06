module Case
    ( compile
    , CaseDef (..)
    )
    where

import TT
import Pretty
import Util.PrettyPrint

data CaseDef r = CaseDef [Name] (Tree r)
data Tree r = PlainTerm (TT r) | Case Name [Alt r]
data AltLHS = Ctor Name [Name] | Wildcard
data Alt r = Alt AltLHS (Tree r)

instance PrettyR r => Pretty (CaseDef r) where
    pretty (CaseDef ns t) =
        text "\\" <> hsep (map pretty ns) <> text "."
        $$ indent (pretty t)

instance PrettyR r => Pretty (Tree r) where
    pretty (PlainTerm tm) = pretty tm
    pretty (Case n alts) =
        text "case" <+> pretty n <+> text "of"
        $$ indent (vcat $ map pretty alts)

instance PrettyR r => Pretty (Alt r) where
    pretty (Alt lhs rhs) = pretty lhs <+> arrow <+> pretty rhs

instance Pretty AltLHS where
    pretty Wildcard = text "_"
    pretty (Ctor cn args) = (hsep . map pretty) (cn : args)

compile :: [Clause r] -> CaseDef r
compile = undefined
