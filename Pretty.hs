{-# LANGUAGE FlexibleInstances #-}
module Pretty (PrettyR(..)) where

import TT
import Util.PrettyPrint

class Show r => PrettyR r where
    prettyCol :: r -> Doc
    prettyApp :: r -> Doc

instance PrettyR Relevance where
    prettyCol x = colon <> showd x <> colon
    prettyApp x = text "-" <> showd x <> text "-"

instance PrettyR () where
    prettyCol _ = colon
    prettyApp _ = text " "

instance PrettyR (Maybe Relevance) where
    prettyCol Nothing = colon
    prettyCol (Just r) = prettyApp r

    prettyApp Nothing = text " "
    prettyApp (Just r) = prettyApp r

instance PrettyR r => Pretty (Program r) where
    pretty (Prog defs) = vcat $ map fmtDef defs
      where
        fmtDef (Def _r n Erased dt) = text n <+> equals <+> fmtDT dt $$ blankLine
        fmtDef (Def r n ty dt) =
            pretty (n, r, ty)
            $$ text n <+> equals <+> fmtDT dt
            $$ blankLine

        fmtDT Axiom = text "(axiom)"
        fmtDT (Fun tm) = pretty tm

instance PrettyR r => Pretty (Name, r, TT r) where
    pretty (n, r, ty) = text n <+> prettyCol r <+> pretty ty

instance PrettyR r => Pretty (TT r) where
    pretty (V n) = text n
    pretty (Bind Pi r n ty tm) = parens (pretty (n, r, ty)) <+> arrow <+> pretty tm
    pretty (Bind Lam _r n Erased tm) = lam <> text n <> dot <+> pretty tm
    pretty (Bind Lam r n ty tm) = lam <> pretty (n, r, ty) <> dot <+> pretty tm
    pretty (App r f x) = parens $ show' r f x
      where
        show' r (App r' f' x') x = show' r' f' x' <> prettyApp r <> showd x
        show' r f x = showd f <> prettyApp r <> showd x
    pretty (Case s alts) =
        text "case" <+> pretty s <+> text "of"
        $$ indent (vcat $ map pretty alts)
    pretty Erased = text "____"
    pretty Type = text "*"

instance PrettyR r => Pretty (Alt r) where
    pretty (DefaultCase tm) = text "_" <+> arrow <+> pretty tm
    pretty (ConCase cn r ns tm) = text cn <+> hsep (map text ns) <+> arrow <+> pretty tm

lam = text "\\"
indent = nest 2
arrow = text "->"
