module Codegen.Scheme (codegen) where

import TT
import TTUtils
import Pretty ()
import Util.PrettyPrint
import Codegen.Common
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

cgBody :: Name -> TT () -> Body () -> Doc
cgBody n ty (Abstract Postulate) = cgCtor n ty
cgBody n ty (Abstract Var) = error $ "let-bound variable: " ++ show n
cgBody n ty (Term tm) = cgTm tm
cgBody n ty (Clauses cs) = cgMatchLambda cs

cgLetRec :: [Def ()] -> Doc -> Doc
cgLetRec ds = cgLet' "letrec*" [(n, cgBody n ty b) | Def n () ty b _cs <- ds]

cgTm :: TT () -> Doc
cgTm (V n) = cgName n
cgTm tm@(I n ty) = error $ "e-instance in codegen: " ++ show tm
cgTm (Bind Lam [Def n () ty (Abstract Var) cs] rhs) = cgLambda n $ cgTm rhs
cgTm (Bind Let ds rhs) = cgLetRec ds $ cgTm rhs
cgTm (App () f x) = cgApp (cgTm f) (cgTm x)
cgTm tm = error $ "can't cg tm: " ++ show tm

cgApp :: Doc -> Doc -> Doc
cgApp f x = parens (f <+> x)

cgCtor :: Name -> TT () -> Doc
cgCtor n ty
    = nestLambdas argNs $
        parens (
            text "list"
            <+> text "'" <> cgName n
            <+> hsep (map cgName argNs)
        )
  where
    argNs = uniqNames $ argNames ty

cgMatchLambda :: [Clause ()] -> Doc
cgMatchLambda cs = nestLambdas ns $ parens (
        text "match" <+> parens (text "list" <+> hsep (map cgName ns))
        $$ indent (vcat $ map cgMatchClause cs)
    )
  where
    ns = [MN "e" i | i <- [0..nargs-1]]
    nargs = maximum [length . snd . unApplyPat $ lhs | Clause pvs lhs rhs <- cs]

cgMatchClause :: Clause () -> Doc
cgMatchClause (Clause pvs lhs rhs)
    = brackets (
        parens (cgClauseLHS patvars lhs)
        $$ indent (cgTm rhs)
    )
  where
    patvars = S.fromList $ map defName pvs

cgClauseLHS :: S.Set Name -> Pat () -> Doc
cgClauseLHS pvs pat =
    hsep [cgPat pvs p | (r, p) <- args]
  where
    (_f, args) = unApplyPat pat

cgPat :: S.Set Name -> Pat () -> Doc
cgPat pvs (PV n)
    | n `S.member` pvs = cgName n
    | otherwise = parens (text "'" <> cgName n)

cgPat pvs pat@(PApp r f x)
    | (PV cn, args) <- unApplyPat pat
    = parens (hsep $ (text "'" <> cgName cn) : map (cgPat pvs . snd) args)

cgPat pvs pat@(PApp r f x) = error $ "can't compile pattern: " ++ show pat

cgPat pvs (PForced tm) = text "_"

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

argNames :: TT () -> [Name]
argNames (Bind Pi ds rhs) = map defName ds ++ argNames rhs
argNames _ = []

cgProgram :: Program () -> Doc
cgProgram prog = 
    parens (text "require-extension" <+> text "matchable")
    $$ parens (
        text "print" $+$ indent (cgTm prog)
    ) -- $+$ parens (text "newline")  -- newline for Racket

codegen :: Codegen
codegen = Codegen
    { cgRun = cgProgram
    , cgExt = "scm"
    }
