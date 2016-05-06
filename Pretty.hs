{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, ConstraintKinds #-}
module Pretty
    ( PrettyR(..), IsRelevance
    , indent, arrow
    ) where

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

instance PrettyR r => Pretty (Clause r) where
    pretty (Clause [] lhs rhs) =
        pretty lhs <+> text "=" <+> pretty rhs
    pretty (Clause pvs lhs rhs) =
        (text "pat" <+> hsep (map prettyPVar pvs) <> text ".")
        $$ indent (pretty $ Clause [] lhs rhs)
      where
        prettyPVar d@(Def _ _ (V Blank) _ _) = pretty d
        prettyPVar d = parens (pretty d)

instance PrettyR r => Pretty (Body r) where
    pretty (Abstract _) = empty
    pretty (Term tm) = text "=" <+> pretty tm
    pretty (Clauses cls) = vcat $ map pretty cls

instance PrettyR r => Pretty (Program r cs) where
    pretty (Prog defs) = vcat $ map (\d -> pretty d $$ blankLine) defs

instance PrettyR r => Pretty (Def r cs) where
    pretty (Def n r ty body cs) =
        case body of
            Abstract Postulate -> text "postulate"
            _ -> empty
        <+> pretty n
        <+> case ty of
                V Blank -> empty
                _       -> prettyCol r <+> pretty ty
        <+> case body of
                Abstract _  -> empty
                Term tm     -> text "=" <+> pretty tm
                Clauses cls -> blankLine $$ indent (vcat $ map pretty cls)
        <+> case cs of
                Nothing -> empty
                Just _  -> text "{- constraints apply -}"

instance PrettyR r => Pretty (TT r) where
    pretty tm = pretty' False tm
      where
        pretty' pp (V n) = pretty n
        pretty' pp (I n ty) = parens (pretty n <+> colon <+> pretty ty)
        pretty' pp (Bind Pi d tm) = parens (pretty d) <+> arrow <+> pretty tm
        pretty' pp (Bind Lam d tm) = parens (lam <> pretty d <> dot <+> pretty tm)
        pretty' pp (Bind Let d tm) =
            blankLine
            $$ indent (text "let" <+> pretty d
                $$ text "in" <+> pretty tm
            )
        pretty' pp (App r (V (UN "S")) x) | Just i <- fromNat x = int $ 1+i
          where
            fromNat (V (UN "Z")) = Just 0
            fromNat (App r (V (UN "S")) x) = (1 +) `fmap` fromNat x
            fromNat _ = Nothing
        pretty' pp (App r f x) = ps $ show' r f x
          where
            ps = if pp then parens else id
            show' r (App r' f' x') x = show' r' f' x' <> prettyApp r <> pretty' True x
            show' r f x = pretty f <> prettyApp r <> pretty' True x

instance PrettyR r => Pretty (Pat r) where
    pretty tm = pretty' False tm
      where
        pretty' pp (PV n) = pretty n
        pretty' pp (PApp r f x) = ps $ show' r f x 
          where
            ps = if pp then parens else id
            show' r (PApp r' f' x') x = show' r' f' x' <> prettyApp r <> pretty' True x
            show' r f x = pretty f <> prettyApp r <> pretty' True x
        pretty' pp (PForced tm) = text "[" <> pretty tm <> text "]"

instance PrettyR r => Show (TT r) where
    show = prettyShow

instance PrettyR r => Show (Pat r) where
    show = prettyShow

instance PrettyR r => Show (Def r cs) where
    show = prettyShow

deriving instance PrettyR r => Show (Clause r)
deriving instance PrettyR r => Show (Body r)
deriving instance PrettyR r => Show (Program r VoidConstrs)

type IsRelevance r = (PrettyR r, Eq r)

instance PrettyR r => Pretty (CaseFun r) where
    pretty (CaseFun ns t) =
        text "\\" <> hsep (map (parens . pretty) ns) <> text "."
        $$ indent (pretty t)

instance PrettyR r => Pretty (Tree r) where
    pretty (PlainTerm tm) = pretty tm
    pretty (Case n alts) =
        text "case" <+> pretty n <+> text "of"
        $$ indent (vcat $ map pretty alts)

instance PrettyR r => Pretty (Alt r) where
    pretty (Alt lhs rhs) = pretty lhs <+> arrow <+> pretty rhs

instance PrettyR r => Pretty (AltLHS r) where
    pretty Wildcard = text "_"
    pretty (Ctor cn args) = (hsep . map pretty) (cn : args)

instance PrettyR r => Pretty (CtorArg r) where
    pretty (PV n) = pretty n
    pretty (Forced tm) = text "[" <> pretty tm <> text "]"

instance PrettyR r => Show (CaseDef r) where
    show = prettyShow

lam = text "\\"
indent = nest 2
arrow = text "->"
