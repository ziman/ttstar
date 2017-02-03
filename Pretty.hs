{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, ConstraintKinds #-}
module Pretty (useUnicode, PrettyR(..), ShowUnicode (..), sup) where

import TT
import Util.PrettyPrint
import qualified Data.Map as M

useUnicode :: Bool
useUnicode = False  -- True

sup :: Char -> Char
sup '0' = '⁰'
sup '1' = '¹'
sup '2' = '²'
sup '3' = '³'
sup '4' = '⁴'
sup '5' = '⁵'
sup '6' = '⁶'
sup '7' = '⁷'
sup '8' = '⁸'
sup '9' = '⁹'
sup 'R' = 'ᴿ'
sup 'E' = 'ᴱ'
sup c = error $ "no unicode superscript for: " ++ show c

class ShowUnicode a where
    showUnicode :: a -> Doc

instance ShowUnicode Relevance where
    showUnicode = text . map sup . show

class Show r => PrettyR r where
    prettyCol :: r -> Doc
    prettyApp :: r -> Doc
    prettyAlt :: r -> Maybe Doc

instance PrettyR Relevance where
    prettyCol x
        | useUnicode = colon <> showUnicode x
        | otherwise  = colon <> showd x <> colon

    prettyApp x
        | useUnicode = text " " <> showUnicode x <> text " "
        | otherwise  = text " -" <> showd x <> text "- "

    prettyAlt r = Just (showd r)

instance PrettyR () where
    prettyCol _ = colon
    prettyApp _ = text " "
    prettyAlt _ = Nothing

instance PrettyR (Maybe Relevance) where
    prettyCol Nothing = colon
    prettyCol (Just r) = prettyCol r

    prettyApp Nothing = text " "
    prettyApp (Just r) = prettyApp r

    prettyAlt Nothing = Nothing
    prettyAlt (Just r) = Just $ showd r

instance Pretty Name where
    pretty = text . show

instance PrettyR r => Pretty (Body r) where
    pretty (Abstract _) = empty
    pretty (Term tm) = text "=" <+> pretty tm
    pretty (Patterns cf) = pretty cf

instance PrettyR r => Pretty (Def r) where
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
                Patterns cf -> text "=" <+> pretty cf
        <+> if M.null cs
                then empty
                else text "{- constraints apply -}"

instance PrettyR r => Pretty (TT r) where
    pretty tm = pretty' False tm
      where
        pretty' pp (V n) = pretty n
        pretty' pp (I n ty) = brackets (pretty n <+> colon <+> pretty ty)
        pretty' pp (Bind Pi [d] tm) = parens (pretty d) <+> text "->" <+> pretty tm
        pretty' pp (Bind Lam [d] tm) = parens (text "\\" <> pretty d <> dot <+> pretty tm)
        pretty' pp (Bind Let [d] tm) =
            blankLine
            $$ indent (text "let" <+> pretty d
                $$ text "in" <+> pretty tm
            )
        pretty' pp (Bind Let ds tm) =
            blankLine
            $$ indent (text "let"
                $$ indent (vcat [
                    pretty d
                    | d <- ds
                ])
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
        pretty' pp (Forced tm) = brackets (pretty' False tm) 
        pretty' pp tm = text "[???" <+> text (show tm) <+> text "???]"

instance PrettyR r => Show (TT r) where
    show = prettyShow

instance PrettyR r => Show (Def r) where
    show = prettyShow

deriving instance PrettyR r => Show (Body r)

instance PrettyR r => Pretty (CaseFun r) where
    pretty (CaseFun [] t) = pretty t
    pretty (CaseFun ns t) =
        text "\\" <> hsep (map prettyParens ns) <> text "."
        $$ indent (pretty t)

instance PrettyR r => Pretty (CaseTree r) where
    pretty (Leaf tm) = pretty tm
    pretty (Case r n alts) =
        text "case" <> prettyApp r <> pretty n <+> text "of"
        $$ indent (vcat $ map pretty alts)

instance PrettyR r => Pretty (Alt r) where
    pretty (Alt lhs rhs) = pretty lhs $$ indent (text "=>" <+> pretty rhs)

instance PrettyR r => Pretty (AltLHS r) where
    pretty Wildcard = text "_"
    pretty (Ctor ct args)
        = pretty ct <+> hsep (map prettyParens args)
    pretty (ForcedVal ftm)
        = brackets (pretty ftm)

instance PrettyR r => Pretty (CtorTag r) where
    pretty (CT cn r)
        = pretty cn <> maybe empty (text "/" <>) (prettyAlt r)
    pretty (CTForced cn)
        = brackets (pretty cn)

prettyParens :: PrettyR r => Def r -> Doc
prettyParens d
    | V Blank <- defType d
    = pretty d

    | otherwise
    = parens $ pretty d

instance PrettyR r => Show (CaseFun r) where
    show = prettyShow

instance PrettyR r => Show (CaseTree r) where
    show = prettyShow

instance PrettyR r => Show (Alt r) where
    show = prettyShow

indent :: Doc -> Doc
indent = nest 2
