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
cgName = text . specialName . map mogrify . show
  where
    specialName n
        | n `elem` specialNames = n ++ "_TT"
        | otherwise = n
    mogrify '\'' = '_'
    mogrify c = c

cgLetDef :: Def () -> Doc -> Doc
cgLetDef (Def n () ty (Abstract Postulate) cs)
    = cgLet [(n, cgCtor n ty)]
cgLetDef (Def n () ty (Term tm) cs)
    = cgLet [(n, cgTm tm)]
cgLetDef (Def n () ty (Patterns cf) cs)
    = cgLet [(n, cgCaseFun cf)]

cgTm :: TT () -> Doc
cgTm (V n) = cgName n
cgTm tm@(I n ty) = error $ "e-instance in codegen: " ++ show tm
cgTm (Bind Lam [Def n () ty (Abstract Var) cs] rhs) = cgLambda n $ cgTm rhs
cgTm (Bind Let ds rhs) = foldr cgLetDef (cgTm rhs) ds
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

cgDef :: Def () -> Doc
cgDef (Def n r ty (Abstract Postulate) cs) = cgDefine n $ cgCtor n ty
cgDef (Def n r ty (Patterns cf) cs) = cgDefine n $ cgCaseFun cf
cgDef (Def n r ty (Term tm) cs) = cgDefine n $ cgTm tm
cgDef d@(Def n r ty b cs) = error $ "can't cg def: " ++ show d

cgCaseTree :: CaseTree () -> Doc
cgCaseTree (Leaf tm) = cgTm tm
cgCaseTree (Case () (V scrutN) alts) =
    cgCase (text "car" `cgApp` cgName scrutN)
        $ map (cgAlt scrutN) alts

cgCaseTree (Case () scrut alts) =
    error $ "can't cg case scrutinee: " ++ show scrut

cgAlt :: Name -> Alt () -> Doc
cgAlt argsN (Alt Wildcard rhs) = parens (text "else" <+> cgCaseTree rhs)
cgAlt argsN (Alt (Ctor () cn ds _eqs) rhs)
    = parens (
        parens (cgName cn)
        <+> cgBinds (map defName ds) argsN (cgCaseTree rhs)
    )

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

cgDefine :: Name -> Doc -> Doc
cgDefine n body = parens (text "define" <+> cgName n $+$ indent body)

cgLambda :: Name -> Doc -> Doc
cgLambda n body = parens (text "lambda" <+> parens (cgName n) $+$ indent body)

cgLet :: [(Name, Doc)] -> Doc -> Doc
cgLet = cgLet' "let"

cgLetStar :: [(Name, Doc)] -> Doc -> Doc
cgLetStar = cgLet' "let*"

cgLet' :: String -> [(Name, Doc)] -> Doc -> Doc
cgLet' letN defs rhs = parens (
        text letN <+> parens (
            hsep [parens (cgName n <+> body) | (n, body) <- defs]
        )
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
argNames (Bind Pi d rhs) = defName d : argNames rhs
argNames _ = []

cgProgram :: Program () -> Doc
cgProgram (Prog defs) = vcat [
    cgDef def $+$ blankLine
    | def <- defs
    ] $+$ text "(print main)"  -- add (newline) for racket

codegen :: Codegen
codegen = Codegen
    { cgRun = cgProgram
    , cgExt = "scm"
    }
