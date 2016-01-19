{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving #-}
module Pretty (PrettyR(..)) where

import TT
import Util.PrettyPrint

class Show r => PrettyR r where
    prettyCol :: r -> Doc
    prettyApp :: r -> Doc

instance PrettyR Relevance where
    prettyCol x = colon <> showd x <> colon
    prettyApp x = text " -" <> showd x <> text "- "

instance PrettyR () where
    prettyCol _ = colon
    prettyApp _ = text " "

instance PrettyR (Maybe Relevance) where
    prettyCol Nothing = colon
    prettyCol (Just r) = prettyApp r

    prettyApp Nothing = text " "
    prettyApp (Just r) = prettyApp r

instance Pretty Name where
    pretty = text . show

instance PrettyR r => Pretty (Program r cs) where
    pretty (Prog defs) = vcat $ map fmtDef defs
      where
        fmtDef (Def n r Erased Nothing cs) = empty
        fmtDef (Def n r Erased mtm cs) = fmtMT n mtm $$ blankLine
        fmtDef (Def n r ty mtm cs) = pretty (n, r, ty) $$ fmtMT n mtm $$ blankLine

        fmtMT n Nothing   = empty
        fmtMT n (Just tm) = pretty n <+> equals <+> pretty tm

instance PrettyR r => Pretty (Name, r, TT r) where
    pretty (n, r, Erased) = pretty n
    pretty (n, r, ty) = pretty n <+> prettyCol r <+> pretty ty

instance PrettyR r => Pretty (TT r) where
    pretty (V n) = pretty n
    pretty (I n ty) = parens (pretty n <+> colon <+> pretty ty)
    pretty (Bind Pi n r ty tm) = parens (pretty (n, r, ty)) <+> arrow <+> pretty tm
    pretty (Bind Lam n r Erased tm) = parens (lam <> pretty n <> dot <+> pretty tm)
    pretty (Bind Lam n r ty tm) = parens (lam <> pretty (n, r, ty) <> dot <+> pretty tm)
    pretty (Bind Pat n r ty tm) = text "pat " <> pretty (n, r, ty) <> dot <+> pretty tm
    pretty (App r (V (UN "S")) x) | Just i <- fromNat x = int $ 1+i
      where
        fromNat (V (UN "Z")) = Just 0
        fromNat (App r (V (UN "S")) x) = (1 +) `fmap` fromNat x
        fromNat _ = Nothing
    pretty (App r f x) = parens $ show' r f x
      where
        show' r (App r' f' x') x = show' r' f' x' <> prettyApp r <> pretty x
        show' r f x = pretty f <> prettyApp r <> pretty x
    pretty (Let d@(Def n r ty mtm Nothing) tm) =
        blankLine
        $$ indent (text "let" <+> pretty d
            $$ text "in" <+> pretty tm
        )
    pretty (Case s alts) =
        blankLine
        $$ indent (
            text "case" <+> pretty s <+> text "of"
            $$ indent (vcat $ map pretty alts)
        )
    pretty Erased = text "____"
    pretty Type = text "*"

instance PrettyR r => Pretty (Alt r) where
    pretty (DefaultCase tm) = text "_" <+> arrow <+> pretty tm
    pretty (ConCase cn tm) = pretty cn <+> hsep (map prettyPat args) <+> arrow <+> pretty rhs
      where
        prettyPat (n, r, Erased) = pretty n
        prettyPat (n, r, ty) = parens $ pretty (n, r, ty)
        (args, rhs) = splitBinder Pat tm

instance PrettyR r => Pretty (Def r VoidConstrs) where
    pretty (Def n r ty Nothing Nothing) = text "postulate" <+> pretty (n, r, ty)
    pretty (Def n r ty (Just tm) Nothing) =
        pretty (n, r, ty)
        $$ indent (equals <+> pretty tm)

instance PrettyR r => Show (TT r) where
    show = prettyShow

deriving instance PrettyR r => Show (Alt r)
deriving instance (Show (cs r), PrettyR r) => Show (Def r cs)

lam = text "\\"
indent = nest 2
arrow = text "->"
