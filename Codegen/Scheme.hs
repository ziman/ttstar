module Codegen.Scheme (codegen) where

import TT.Core
import TT.Utils
import TT.Pretty
import Util.PrettyPrint
import qualified Data.Set as S

indent :: Doc -> Doc
indent = nest 2

specialNames :: [String]
specialNames =
    [ "apply"
    , "append"
    , "not"
    , "reverse"
    ]

cgName :: Name -> Doc
cgName = text . specialName . concatMap mogrify . show
  where
    specialName n
        | n `elem` specialNames = n ++ "_TT"
        | otherwise = n
    mogrify '\'' = "_"
    mogrify c = [c]

-- flavours of `let` in Scheme:
-- http://www.cs.rpi.edu/academics/courses/fall00/ai/scheme/reference/schintro-v14/schintro_126.html

cgBody :: PrettyR r => Name -> TT r -> Body r -> Doc
cgBody n ty (Abstract (Foreign code)) = text code
cgBody n ty (Abstract Postulate) = cgCtor n ty  -- XXX: shouldn't this throw errors?
cgBody n ty (Abstract Constructor) = cgCtor n ty
cgBody n ty (Abstract Var) = error $ "let-bound variable: " ++ show n
cgBody n ty (Term tm) = cgTm tm
cgBody n ty (Clauses []) = symbol "CannotBeCalled"  -- can appear in unerased code
cgBody n ty (Clauses cs) = cgMatchLambda cs

symbol :: String -> Doc
symbol s = text "'" <> text s

cgOmitted :: Doc
cgOmitted = text "'_"

cgLetRec :: PrettyR r => [Def r] -> Doc -> Doc
cgLetRec ds = cgLet' "letrec*" [(n, cgBody n ty b) | Def n r ty b <- ds]

cgTm :: PrettyR r => TT r -> Doc
cgTm (V n) = cgName n
cgTm tm@(EI n ty) = error $ "e-instance in codegen: " ++ show tm
cgTm (Bind Lam [Def n r ty (Abstract Var)] rhs) = cgLambda n $ cgTm rhs
cgTm (Bind Let ds rhs) = cgLetRec ds $ cgTm rhs
cgTm (Bind Pi ds rhs) = cgOmitted
cgTm (App r f x) = cgApp (cgTm f) (cgTm x)
cgTm tm = error $ "can't cg tm: " ++ show tm

cgApp :: Doc -> Doc -> Doc
cgApp f x = parens (f <+> x)

cgCtor :: Name -> TT r -> Doc
cgCtor n ty
    = nestLambdas argNs $
        text"`" <> parens (
            cgName n
            <+> hsep [text "," <> cgName n | n <- argNs]
        )
  where
    argNs = uniqNames $ argNames ty

cgMatchLambda :: PrettyR r => [Clause r] -> Doc
cgMatchLambda cs = nestLambdas ns $ parens (
        text "match" <+> parens (text "list" <+> hsep (map cgName ns))
        $$ indent (vcat $ map cgMatchClause cs)
    )
  where
    ns = [MN "e" i | i <- [0..nargs-1]]
    nargs = maximum [length . snd . unApplyPat $ lhs | Clause pvs lhs rhs <- cs]

cgMatchClause :: PrettyR r => Clause r -> Doc
cgMatchClause (Clause pvs lhs rhs)
    = parens (
        parens (cgClauseLHS patvars lhs)
        $$ indent (cgTm rhs)
    )
  where
    patvars = S.fromList $ map defName pvs

cgClauseLHS :: PrettyR r => S.Set Name -> Pat r -> Doc
cgClauseLHS pvs pat =
    hsep [cgPat pvs p | (r, p) <- args]
  where
    (_f, args) = unApplyPat pat

cgPat :: PrettyR r => S.Set Name -> Pat r -> Doc
cgPat pvs (PV Blank) = text "_"

cgPat pvs (PV n)
    | n `S.member` pvs = cgName n
    | otherwise = parens (text "'" <> cgName n)

cgPat pvs pat@(PApp r f x)
    | (PV cn, args) <- unApplyPat pat
    = cgPatApp cn args
    | (PForced tm, args) <- unApplyPat pat
    = cgPatApp Blank args
  where
    cgPatApp cn args = parens (hsep $ cgPName cn : map (cgPat pvs . snd) args)
    cgPName Blank = text "_"
    cgPName cn = text "'" <> cgName cn

cgPat pvs pat@(PApp r f x) = error $ "can't compile pattern: " ++ show pat

cgPat pvs (PForced tm) = text "_"

cgPat pvs (PHead _f) = text "_"

cgLambda :: Name -> Doc -> Doc
cgLambda n body = parens (text "lambda" <+> parens (cgName n) $+$ indent body)

cgLet' :: String -> [(Name, Doc)] -> Doc -> Doc
cgLet' letN [(n, body)] rhs = parens (
        text letN <+> parens (
            parens (cgName n <+> body)
        )
        $+$ indent rhs
    )
cgLet' letN defs rhs = parens (
        text letN <+> text "("
        $+$ indent (
            vcat [parens (cgName n <+> body) | (n, body) <- defs]
        )
        $+$ text ")"
        $+$ indent rhs
    )

nestLambdas :: [Name] -> Doc -> Doc
nestLambdas [] = id
nestLambdas (n:ns) = cgLambda n . nestLambdas ns

uniqNames :: [Name] -> [Name]
uniqNames ns =
    [ n ||| (UN $ "e" ++ show i)
    | (i, n) <- zip [0::Integer ..] ns
    ]
  where
    (|||) :: Name -> Name -> Name
    (|||) Blank n = n
    (|||) m     n = m

argNames :: TT r -> [Name]
argNames (Bind Pi ds rhs) = map defName ds ++ argNames rhs
argNames _ = []

codegen :: PrettyR r => Program r -> Doc
codegen prog = 
    text "(import (chicken process-context))"
    $$ parens (text "require-extension" <+> text "matchable")
    $$ text "(define Type '(Type))"
    $$ text "(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))"
    $$ text "(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))"
    $$ text "(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))"
    $$ parens (
        text "print" $+$ indent (cgTm prog)
    ) -- $+$ parens (text "newline")  -- newline for Racket
