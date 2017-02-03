module Codegen.Scheme (codegen) where

import TT
import Pretty ()
import Util.PrettyPrint
import Codegen.Common

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
cgBody n ty (Patterns cf) = cgCaseFun cf

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

cgCaseFun :: CaseFun () -> Doc
cgCaseFun (CaseFun args ct) = 
    nestLambdas argNs $ cgCaseTree ct
  where
    argNs = uniqNames $ map defName args

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

cgCaseTree :: CaseTree () -> Doc
cgCaseTree (Leaf tm) = cgTm tm
cgCaseTree (Case () (V scrutN) alts) =
    cgCase (text "car" `cgApp` cgName scrutN)
        $ map (cgAlt scrutN) alts

cgCaseTree (Case () scrut alts) =
    error $ "can't cg case scrutinee: " ++ show scrut

cgAlt :: Name -> Alt () -> Doc
cgAlt argsN (Alt Wildcard rhs) = parens (text "else" <+> cgCaseTree rhs)
cgAlt argsN (Alt (Ctor ct ds) rhs)
    = parens (
        parens (cgName $ ctName ct)
        <+> cgBinds (map defName ds) argsN (cgCaseTree rhs)
    )
cgAlt argsN (Alt (ForcedPat ftm) rhs) = cgCaseTree rhs

cgBinds :: [Name] -> Name -> Doc -> Doc
cgBinds [] args rhs = rhs
cgBinds (n:ns) args rhs =
    cgLetStar [
        (subvalsN, cgApp (text "cdr") (cgName args)),
        (n, cgApp (text "car") (cgName subvalsN))
    ] $ cgBinds ns subvalsN rhs
  where
    subvalsN = let UN s = n in UN ("_args-" ++ s)

cgCase :: Doc -> [Doc] -> Doc
cgCase scrut alts = parens (text "case" <+> scrut $+$ indent (vcat alts))

cgLambda :: Name -> Doc -> Doc
cgLambda n body = parens (text "lambda" <+> parens (cgName n) $+$ indent body)

cgLetStar :: [(Name, Doc)] -> Doc -> Doc
cgLetStar = cgLet' "let*"

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
cgProgram prog = parens (
    text "print" $+$ indent (cgTm prog)
  ) -- $+$ parens (text "newline")  -- newline for Racket

codegen :: Codegen
codegen = Codegen
    { cgRun = cgProgram
    , cgExt = "scm"
    }
