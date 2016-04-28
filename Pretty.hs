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

instance PrettyR r => Pretty (Clause r) where
    pretty (Clause [] lhs rhs) =
        pretty lhs <+> text " = " <+> pretty rhs
    pretty (Clause pvs lhs rhs) =
        (text "pat" <+> hsep (map (parens . pretty) pvs) <> text ".")
        $$ indent (pretty $ Clause [] lhs rhs)

instance PrettyR r => Pretty (Body r) where
    pretty (Abstract _) = empty
    pretty (Term tm) = text "=" <+> pretty tm
    pretty (Clauses cls) = vcat $ map pretty cls

instance PrettyR r => Pretty (Program r cs) where
    pretty (Prog defs) = vcat $ map fmtDef defs
      where
        fmtDef (Def n r ty (Abstract Postulate) cs)
            = text "postulate" <+> pretty (Def n r ty (Abstract Postulate) Nothing)
                $$ blankLine
        fmtDef (Def n r Erased body cs) = indent (pretty body) $$ blankLine
        fmtDef (Def n r ty body cs)
            = pretty (Def n r ty (Abstract Var) Nothing)
                $$ indent (pretty body) $$ blankLine

instance PrettyR r => Pretty (Def r cs) where
    pretty (Def n r Erased (Abstract _) Nothing) = pretty n
    pretty (Def n r ty     (Abstract _) Nothing) = pretty n <+> prettyCol r <+> pretty ty
    pretty (Def n r ty    (Term   tm) Nothing) = pretty n <+> prettyCol r <+> pretty ty <+> text "=" <+> pretty tm
    pretty (Def n r ty    (Clauses cls) Nothing)
        = pretty (Def n r ty (Abstract Var) Nothing)
            $$ indent (vcat $ map pretty cls)
    pretty (Def n r ty cls (Just cs))
        = pretty (Def n r ty cls Nothing) <+> text "{- constraints apply -}"

instance PrettyR r => Pretty (TT r) where
    pretty (V n) = pretty n
    pretty (I n ty) = parens (pretty n <+> colon <+> pretty ty)
    pretty (Bind Pi d tm) = parens (pretty d) <+> arrow <+> pretty tm
    pretty (Bind Lam d tm) = parens (lam <> pretty d <> dot <+> pretty tm)
    pretty (Bind Let d tm) =
        blankLine
        $$ indent (text "let" <+> pretty d
            $$ text "in" <+> pretty tm
        )
    pretty (App r (V (UN "S")) x) | Just i <- fromNat x = int $ 1+i
      where
        fromNat (V (UN "Z")) = Just 0
        fromNat (App r (V (UN "S")) x) = (1 +) `fmap` fromNat x
        fromNat _ = Nothing
    pretty (App r f x) = parens $ show' r f x
      where
        show' r (App r' f' x') x = show' r' f' x' <> prettyApp r <> pretty x
        show' r f x = pretty f <> prettyApp r <> pretty x
    pretty (Forced tm) = text "[" <> pretty tm <> text "]"
    pretty Erased = text "____"
    pretty Type = text "*"

instance PrettyR r => Show (TT r) where
    show = prettyShow

deriving instance (Show (cs r), PrettyR r) => Show (Def r cs)
deriving instance PrettyR r => Show (Clause r)
deriving instance PrettyR r => Show (Body r)

lam = text "\\"
indent = nest 2
arrow = text "->"
