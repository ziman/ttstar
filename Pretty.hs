{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, ConstraintKinds #-}
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

instance PrettyR r => Pretty (Body r) where
    pretty (Abstract _) = empty
    pretty (Term tm) = text "=" <+> pretty tm
    pretty (Patterns cf) = pretty cf

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
                Patterns cf -> blankLine $$ indent (pretty cf)
        <+> case cs of
                Nothing -> empty
                Just _  -> text "{- constraints apply -}"

instance PrettyR r => Pretty (TT r) where
    pretty tm = pretty' False tm
      where
        pretty' pp (V n) = pretty n
        pretty' pp (I n ty) = parens (pretty n <+> colon <+> pretty ty)
        pretty' pp (Bind Pi d tm) = parens (pretty d) <+> text "->" <+> pretty tm
        pretty' pp (Bind Lam d tm) = parens (text "\\" <> pretty d <> dot <+> pretty tm)
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

instance PrettyR r => Show (TT r) where
    show = prettyShow

instance PrettyR r => Show (Def r cs) where
    show = prettyShow

deriving instance PrettyR r => Show (Body r)
deriving instance PrettyR r => Show (Program r VoidConstrs)

instance PrettyR r => Pretty (CaseFun r) where
    pretty (CaseFun ns t) =
        text "\\" <> hsep (map (parens . pretty) ns) <> text "."
        $$ indent (pretty t)

instance PrettyR r => Pretty (CaseTree r) where
    pretty (PlainTerm tm) = pretty tm
    pretty (Case n alts) =
        text "case" <+> pretty n <+> text "of"
        $$ indent (vcat $ map pretty alts)

instance PrettyR r => Pretty (Alt r) where
    pretty (Alt lhs rhs) = pretty lhs $$ indent (text "=>" <+> pretty rhs)

instance PrettyR r => Pretty (AltLHS r) where
    pretty Wildcard = text "_"
    pretty (Ctor cn args eqs)
        = pretty cn
            <+> hsep (map (parens . pretty) args)
            $+$ indent (
                    foldr ($$) empty [text "|" <+> pretty n <+> text "=" <+> pretty tm | (n, tm) <- eqs]
                )

instance PrettyR r => Show (CaseFun r) where
    show = prettyShow

indent = nest 2
