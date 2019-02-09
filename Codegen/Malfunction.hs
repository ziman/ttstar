{-# LANGUAGE OverloadedStrings #-}
module Codegen.Malfunction (codegen) where

import Data.Functor
import Data.Traversable
import Control.Monad.Trans.State
import qualified Data.Map as M

import IR.Core
import Util.PrettyPrint

data CGState = CGS
    { cgsCtorTags :: M.Map IName Int
    }

type CG a = State CGState a

ctorTag :: IName -> CG Int
ctorTag n = do
    CGS{cgsCtorTags} <- get
    case M.lookup n cgsCtorTags of
        Just i -> return i
        Nothing -> do
            let i = M.size cgsCtorTags
            modify $ \cgs -> cgs{cgsCtorTags = M.insert n i cgsCtorTags}
            return i

indent :: Doc -> Doc
indent = nest 2

codegen :: IR -> Doc
codegen prog = evalState cg (CGS M.empty)
  where
    (defs, entryPoint) = letPrefix prog
    cg = do
        defs' <- for defs $ \(n,d) -> cgDef n d <&> ($$ blankLine)
        entryPoint' <- cgTm entryPoint
        return $ parens ("module"
            $$ indent (
                vcat defs'
                $$ parens ("_" <+> entryPoint')
                $$ parens ("export")
            ))

pv :: Int -> Doc
pv i = "$pv" <> int i

cgDef :: IName -> IBody -> CG Doc
cgDef n b = parens . (cgName n <+>) <$> cgBody n b

cgTm :: IR -> CG Doc
cgTm (IV n) = pure $ cgName n
cgTm (ILam n rhs) = cgLambda n <$> cgTm rhs
cgTm (ILet n body rhs) = do
    ds <- for ((n,body):ls) $ \(n,b) -> do
        b' <- cgBody n b
        return (n, b')
    rhs'' <- cgTm rhs'
    return (blankLine $$ indent (cgLet ds rhs''))
  where
    (ls, rhs') = letPrefix rhs

cgTm tm@(IApp _ _)
    | (f, xs) <- unApp [] tm
    = cgApp <$> cgTm f <*> traverse cgTm xs
cgTm (IError s) = pure $ cgApp "error" [text $ show s]

unApp :: [IR] -> IR -> (IR, [IR])
unApp acc (IApp f x) = unApp (x : acc) f
unApp acc tm = (tm, acc)

letPrefix :: IR -> ([(IName, IBody)], IR)
letPrefix (ILet n body rhs) = let (ls,ir) = letPrefix rhs in ((n,body):ls, ir)
letPrefix ir = ([], ir)

cgBody :: IName -> IBody -> CG Doc
cgBody n (IConstructor arity) = cgCtor n arity
cgBody n (IForeign code) = pure $ text code
cgBody n (ICaseFun pvs ct) = nestLambdas (map pv pvs) <$> cgCaseTree ct

cgCaseTree :: ICaseTree -> CG Doc
cgCaseTree (ILeaf tm)
    = cgTm tm
cgCaseTree (ICase v [ICtor IBlank pvs rhs])
    = cgUnpack v pvs <$> cgCaseTree rhs
cgCaseTree (ICase v [IDefault rhs])
    = cgCaseTree rhs
cgCaseTree (ICase v alts)
    = cgCase (pv v) <$> traverse (cgAlt v) alts

cgAlt :: Int -> IAlt -> CG Doc
cgAlt _ (IDefault rhs) = do
    rhs' <- cgCaseTree rhs
    return $ parens (parens("tag" <+> "_") <+> rhs')
{-
cgAlt _ (ICtor IBlank pvs rhs) = parens (
    parens ("_" <+> hsep (map pv pvs))
    <+> cgCaseTree rhs
  )
-}
cgAlt v (ICtor cn pvs rhs) = do
    tag <- ctorTag cn
    rhs' <- cgCaseTree rhs
    return $ parens (cgTag tag <+> cgUnpack v pvs rhs')

cgTag :: Int -> Doc
cgTag tag = parens ("tag" <+> int tag)

cgCase :: Doc -> [Doc] -> Doc
cgCase scrut alts = parens ("switch" <+> scrut $$ indent (vcat alts))

cgCtor :: IName -> Int -> CG Doc
cgCtor cn arity = do
    tag <- ctorTag cn
    return $ nestLambdas argNs
        $ cgForm "block" (cgTag tag : argNs)
  where
    argNs = ["$e" <> int i | i <- [0..arity-1]]

cgUnpack :: Int -> [Int] -> Doc -> Doc
cgUnpack scrut [] rhs = rhs
cgUnpack scrut vs rhs = parens (
    "let" <+> parens (hsep
        [ parens (pv v <+> parens ("field" <+> int i <+> pv scrut))
        | (i, v) <- zip [0..] vs
        ]
    )
    $$ indent rhs
  )

nestLambdas :: [Doc] -> Doc -> Doc
nestLambdas [] rhs = rhs
nestLambdas ns rhs = parens (
    "lambda" <+> parens (hsep ns)
    $$ indent rhs
  )

cgForm :: Doc -> [Doc] -> Doc
cgForm f xs = parens (f <+> hsep xs)

cgApp :: Doc -> [Doc] -> Doc
cgApp f xs = cgForm "apply" (f : xs)

specialNames :: [String]
specialNames =
    [ "apply"
    , "append"
    , "not"
    , "reverse"
    ]

cgName :: IName -> Doc
cgName IBlank = "_"
cgName (IPV i) = pv i
cgName (IUN n) = ("$" <>) . text . specialName . concatMap mogrify $ n
  where
    specialName n
        | n `elem` specialNames = n ++ "_TT"
        | otherwise = n
    mogrify '\'' = "_"
    mogrify c = [c]

cgLambda :: IName -> Doc -> Doc
cgLambda n body = parens ("lambda" <+> parens (cgName n) $+$ indent body)

cgLet :: [(IName, Doc)] -> Doc -> Doc
cgLet [(n, body)] rhs = parens (
        "letrec" <+> parens (
            parens (cgName n <+> body)
        )
        $+$ indent rhs
    )
cgLet defs rhs = parens (
        "letrec*" <+> "("
        $+$ indent (
            vcat [parens (cgName n <+> body) | (n, body) <- defs]
        )
        $+$ ")" <+> rhs
    )
