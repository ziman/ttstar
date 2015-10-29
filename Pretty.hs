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

instance PrettyR r => Pretty (Program r cs) where
    pretty (Prog defs) = vcat $ map fmtDef defs
      where
        fmtDef (Def n r Erased Nothing cs) = empty
        fmtDef (Def n r Erased mtm cs) = fmtMT n mtm $$ blankLine
        fmtDef (Def n r ty mtm cs) = pretty (n, r, ty) $$ fmtMT n mtm $$ blankLine

        fmtMT n Nothing   = empty
        fmtMT n (Just tm) = text n <+> equals <+> pretty tm

instance PrettyR r => Pretty (Name, r, TT r) where
    pretty (n, r, Erased) = text n
    pretty (n, r, ty) = text n <+> prettyCol r <+> pretty ty

instance PrettyR r => Pretty (Name, r, r, TT r) where
    pretty (n, r, rr, Erased) = text n
    pretty (n, r, rr, ty) = text n <+> prettyCol rr <> prettyCol r <+> pretty ty

instance PrettyR r => Pretty (TT r) where
    pretty (V n) = text n
    pretty (Bind Pi n r ty rr tm) = parens (pretty (n, r, rr, ty)) <+> arrow <+> pretty tm
    pretty (Bind Lam n r Erased rr tm) = lam <> text n <> dot <+> pretty tm
    pretty (Bind Lam n r ty rr tm) = lam <> pretty (n, r, rr, ty) <> dot <+> pretty tm
    pretty (Bind Pat n r ty rr tm) = text "pat " <> pretty (n, r, ty) <> dot <+> pretty tm
    pretty (App pi_rr r (V "S") x) | Just i <- fromNat x = int $ 1+i
      where
        fromNat (V "Z") = Just 0
        fromNat (App pi_rr r (V "S") x) = (1 +) `fmap` fromNat x
        fromNat _ = Nothing
    pretty (App pi_rr r f x) = parens $ show' pi_rr r f x
      where
        show' pi_rr r (App pi_rr' r' f' x') x = show' pi_rr' r' f' x' <> prettyApp pi_rr <> prettyApp r <> pretty x
        show' pi_rr r f x = pretty f <> prettyApp pi_rr <> prettyApp r <> pretty x
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
    pretty (ConCase cn tm) = text cn <+> hsep (map prettyPat args) <+> arrow <+> pretty rhs
      where
        prettyPat (n, r, Erased) = text n
        prettyPat (n, r, ty) = parens $ pretty (n, r, ty)
        (args, rhs) = splitBinder Pat tm

instance PrettyR r => Pretty (Def r Void) where
    pretty (Def n r ty Nothing Nothing) = text "postulate" <+> pretty (n, r, ty)
    pretty (Def n r ty (Just tm) Nothing) =
        pretty (n, r, ty)
        $$ indent (equals <+> pretty tm)

instance PrettyR r => Show (TT r) where
    show = prettyShow

deriving instance PrettyR r => Show (Alt r)
deriving instance (Show cs, PrettyR r) => Show (Def r cs)

lam = text "\\"
indent = nest 2
arrow = text "->"
