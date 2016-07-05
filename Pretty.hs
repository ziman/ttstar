{-# LANGUAGE FlexibleContexts, FlexibleInstances, StandaloneDeriving, ConstraintKinds #-}
module Pretty (useUnicode, PrettyR(..), ShowUnicode (..), sup) where

import Data.Char

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

instance PrettyR Relevance where
    prettyCol x
        | useUnicode = colon <> showUnicode x
        | otherwise  = colon <> showd x <> colon

    prettyApp x
        | useUnicode = text " " <> showUnicode x <> text " "
        | otherwise  = text " -" <> showd x <> text "- "

instance PrettyR () where
    prettyCol _ = colon
    prettyApp _ = text " "

instance PrettyR (Maybe Relevance) where
    prettyCol Nothing = colon
    prettyCol (Just r) = prettyCol r

    prettyApp Nothing = text " "
    prettyApp (Just r) = prettyApp r

instance Pretty Name where
    pretty = text . show

instance PrettyR r => Pretty (Body r) where
    pretty (Abstract _) = empty
    pretty (Term tm) = text "=" <+> pretty tm

instance PrettyR r => Pretty (Program r) where
    pretty (Prog defs) = vcat $ map (\d -> pretty d $$ blankLine) defs

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
        <+> if M.null cs
                then empty
                else text "{- constraints apply -}"

instance PrettyR r => Pretty (TT r) where
    pretty tm = pretty' False tm
      where
        pretty' pp (V n) = pretty n
        pretty' pp (I n ty) = brackets (pretty n <+> colon <+> pretty ty)
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

        pretty' pp (Case r s (V Blank) alts) =
            blankLine $$ indent (
                text "case" <+> pretty s <+> text "of"
                $$ indent (vcat $ map pretty alts)
            )

        pretty' pp (Case r s ty alts) =
            blankLine $$ indent (
                text "case" <> prettyApp r <+> pretty s <+> text "returns" <+> pretty ty <> text "."
                $$ indent (vcat $ map pretty alts)
            )

instance PrettyR r => Show (TT r) where
    show = prettyShow

instance PrettyR r => Show (Def r) where
    show = prettyShow

deriving instance PrettyR r => Show (Body r)
deriving instance PrettyR r => Show (Program r)

instance PrettyR r => Pretty (Alt r) where
    pretty (Alt lhs rhs) = pretty lhs $$ indent (text "=>" <+> pretty rhs)

instance PrettyR r => Pretty (AltLHS r) where
    pretty Wildcard = text "_"
    pretty (Ctor cn args eqs)
        = pretty cn
            <+> hsep (map prettyParens args)
            $+$ indent (
                    foldr ($$) empty [text "|" <+> pretty n <+> text "=" <+> pretty tm | (n, tm) <- eqs]
                )

prettyParens :: PrettyR r => Def r -> Doc
prettyParens d
    | V Blank <- defType d
    = pretty d

    | otherwise
    = parens $ pretty d

instance PrettyR r => Show (Alt r) where
    show = prettyShow

instance PrettyR r => Show (AltLHS r) where
    show = prettyShow

indent = nest 2
