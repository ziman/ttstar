module Codegen.SchemeIR (codegen) where

import IR.Core
import Util.PrettyPrint

indent :: Doc -> Doc
indent = nest 2

codegen :: IR -> Doc

codegen prog = 
    vcat [cgDef n d $$ blankLine | (n,d) <- defs]
    $$ parens (text "display" <+> cgTm entryPoint)
    $$ parens (text "newline")
  where
    -- (defs, entryPoint) = letPrefix prog
    -- ^^ the above doesn't work because (define) does not seem
    -- to be mutually recursive, at least in Chicken
    (defs, entryPoint) = ([], prog)

pv :: Int -> Doc
pv i = text "_pv" <> int i

cgDef :: IName -> IBody -> Doc
cgDef n b = parens (text "define" <+> cgName n <+> cgBody n b)

cgTm :: IR -> Doc
cgTm (IV n) = cgName n
cgTm (ILam n rhs) = cgLambda n $ cgTm rhs
cgTm (ILet n body rhs) = blankLine $$ indent (cgLet ds $ cgTm rhs')
  where
    (ls, rhs') = letPrefix rhs
    ds = [(n, cgBody n b) | (n, b) <- (n, body) : ls]

cgTm (IApp f x) = cgApp (cgTm f) (cgTm x)
cgTm (IError s) = cgApp (text "error") (text $ show s)

letPrefix :: IR -> ([(IName, IBody)], IR)
letPrefix (ILet n body rhs) = let (ls,ir) = letPrefix rhs in ((n,body):ls, ir)
letPrefix ir = ([], ir)

cgBody :: IName -> IBody -> Doc
cgBody n (IConstructor arity) = cgCtor n arity
cgBody n (IForeign code) = text code
cgBody n (ICaseFun pvs ct) = nestLambdas (map pv pvs) rhs
  where
    {-
    -- use instead of `rhs` above
    dbg = parens (text "begin"
        <+> parens (hsep $ text "print" : (text "'" <> cgName n) : map pv pvs)
        <+> rhs
      )
    -}
    rhs = cgCaseTree ct

cgCaseTree :: ICaseTree -> Doc
cgCaseTree (ILeaf tm)
    = cgTm tm
cgCaseTree (ICase v [ICtor IBlank pvs rhs])
    = cgUnpack v pvs (cgCaseTree rhs)
cgCaseTree (ICase v [IDefault rhs])
    = cgCaseTree rhs
cgCaseTree (ICase v alts)
    = cgCase v (map (cgAlt v) alts)

cgAlt :: Int -> IAlt -> Doc
{-
cgAlt (IDefault rhs) = parens (text "_" <+> cgCaseTree rhs)
{-
cgAlt (ICtor IBlank pvs rhs) = parens (
    parens (text "_" <+> hsep (map pv pvs))
    <+> cgCaseTree rhs
  )
-}
cgAlt (ICtor cn pvs rhs) = parens (
    parens (cgName cn <+> hsep (map pv pvs))
    <+> cgCaseTree rhs
  )
-}
cgAlt s (IDefault rhs) = parens (text "else" <+> cgCaseTree rhs)
cgAlt s (ICtor IBlank pvs rhs) = parens (
    text "else" <+> cgUnpack s pvs (cgCaseTree rhs)
  )
cgAlt s (ICtor cn pvs rhs) = parens (
    parens (cgName cn) <+> cgUnpack s pvs (cgCaseTree rhs)
  )

cgCase :: Int -> [Doc] -> Doc
--cgCase scrut alts = parens (text "rts-case" <+> scrut $$ indent (vcat alts))
cgCase scrut alts = parens (
    text "case" <+> parens (text "car" <+> pv scrut)
    $$ vcat alts
  )

cgCtor :: IName -> Int -> Doc
cgCtor n arity
    -- = parens (text "constructor" <+> cgName n <+> hsep argNs)
    = nestLambdas argNs (text "`" <> parens (cgName n <+> hsep [text "," <> n | n <- argNs]))
  where
    argNs = [text "e" <> int i | i <- [0..arity-1]]

cgUnpack :: Int -> [Int] -> Doc -> Doc
cgUnpack scrut [] rhs = rhs
cgUnpack scrut vs rhs = parens (
    text "let*" <+> parens (
        parens (pv scrut <+> parens (text "cdr" <+> pv scrut))
        <+> hsep [
            parens (pv v <+> parens (text "car" <+> pv scrut))
            <+> parens (pv scrut <+> parens (text "cdr" <+> pv scrut))
            | v <- vs
        ]
    )
    $$ indent rhs
  )
{-
cgUnpack scrut vs rhs = parens (
    text "rts-unpack" <+> parens (text "cdr" <+> pv scrut) <+> parens (hsep $ map pv vs)
    $$ indent rhs
  )
-}

nestLambdas :: [Doc] -> Doc -> Doc
nestLambdas [] rhs = rhs
nestLambdas (n:ns) rhs = parens (
    text "lambda" <+> parens n
    $+$ indent (nestLambdas ns rhs)
  )
{-
nestLambdas [n] rhs = parens (text "lambda" <+> parens n $+$ indent rhs)
nestLambdas ns rhs = parens (
    text "curried-lambda" <+> parens (hsep ns)
    $$ indent rhs
  )
-}

cgApp :: Doc -> Doc -> Doc
cgApp f x = parens (f <+> x)

specialNames :: [String]
specialNames =
    [ "apply"
    , "append"
    , "not"
    , "reverse"
    ]

cgName :: IName -> Doc
cgName IBlank = text "_"
cgName (IUN n) = text . specialName . concatMap mogrify $ n
  where
    specialName n
        | n `elem` specialNames = n ++ "_TT"
        | otherwise = n
    mogrify '\'' = "_"
    mogrify c = [c]

cgLambda :: IName -> Doc -> Doc
cgLambda n body = parens (text "lambda" <+> parens (cgName n) $+$ indent body)

cgLet :: [(IName, Doc)] -> Doc -> Doc
cgLet [(n, body)] rhs = parens (
        text "letrec" <+> parens (
            parens (cgName n <+> body)
        )
        $+$ indent rhs
    )
cgLet defs rhs = parens (
        text "letrec*" <+> text "("
        $+$ indent (
            vcat [parens (cgName n <+> body) | (n, body) <- defs]
        )
        $+$ text ")" <+> rhs
    )
