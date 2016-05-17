{-# LANGUAGE FlexibleInstances #-}
module Explorer (genHtml) where

import TT

import Erasure.Meta
import Erasure.Check
import Erasure.Solve

import Control.Applicative
import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import Prelude hiding (div, span)
import qualified Data.Set as S
import qualified Data.Map as M

import Control.Monad.Trans.Reader

type PP = Reader (Uses Meta)

class Html a where
    html :: a -> PP String

instance Html (Program Meta) where
    html (Prog defs) = html defs

instance Html [Def Meta] where
    html ds = ul' "defs" <$> traverse html ds

table :: String -> [[String]] -> String
table cls rows =
    element "table" "cellspacing=\"0\" cellpadding=\"0\"" cls
        $ unlines [
            element "tr" "" ""
                $ unlines [
                    element "td" "" "" cell
                    | cell <- row
                ]
            | row <- rows
        ]

horiz :: [String] -> String
horiz ss = table "horiz-pair" [ss]

vert :: [String] -> String
vert ss = table "vert-pair" [[s] | s <- ss]

horiz' :: [PP String] -> String
horiz' = fmap horiz . sequenceA

vert' :: [PP String] -> String
vert' = fmap vert . sequenceA

element :: String -> String -> String -> String -> String
element elm extra cls body
    = "<" ++ elm ++ " class=\"" ++ cls ++ "\" " ++ extra ++ ">" ++ body ++ "</" ++ elm ++ ">"

div :: String -> String -> String
div = element "div" ""

span :: String -> String -> String
span = element "span" ""

ul :: String -> String -> String
ul = element "ul" ""

ul' :: String -> [String] -> String
ul' cls = ul cls . unlines . map (li "")

li :: String -> String -> String
li = element "li" ""

link :: String -> String -> String
link = element "a" "href=\"#\""

infixr 3 <++>
(<++>) :: PP String -> PP String -> PP String
(<++>) = liftA2 (++)

instance Html Meta where
    html (Fixed R) = pure $ span "rel rel-R" " :<sub>R</sub> "
    html (Fixed E) = pure $ span "rel rel-E" " :<sub>E</sub> "
    html (MVar i)  = pure $ span ("rel mvar-num-" ++ show i) (" :<sub>" ++ show i ++ "</sub> ")

instance Html Name where
    html n = pure $ span ("name name-" ++ show n) (show n)

op :: String -> String
op = span "op"

op' :: String -> PP String
op' = pure . op

nrty :: Name -> Meta -> TT Meta -> PP String
nrty n r ty = do
    uses <- ask
    let
        cls | r `S.member` uses = "nrty-R"
            | otherwise         = "nrty-E erased"

        wrap
            | Fixed _ <- r = span ("nrty " ++ cls)
            | MVar  i <- r = span ("nrty nrty-" ++ show i ++ " " ++ cls)

    erasedSpan r =<< (html n <++> html r <++> html ty <++> pure "\n")

parens :: String -> String
parens s = span "paren" "(" ++ s ++ span "paren" ")"

instance Html (Def Meta) where
    html (Def n r ty (Abstract _) cs) = nrty n r ty
    html (Def n r ty (Term tm) cs) = nrty n r ty <++> pure " = " <++> html tm
    html (Def n r ty (Patterns cf) cs) =
      div "def-pat" <$> (
        (div "def-pat-type" <$> nrty n r ty)
        <++> pure " = "
        <++> (div "def-pat-body" <$> html cf)
      )

instance Html (CaseFun Meta) where
    html (CaseFun [] ct) = html ct
    html (CaseFun args ct) =
        div "cfun" <$> (
            (div "cfun-lam" <$> pure "&lambda; " <++> traverse html args <++> pure ".")
            <++> (div "cfun-tree" <$> html ct)
        )

instance Html (CaseTree Meta) where
    html (Leaf tm) = html tm
    html (Case r n alts) =
        div "case" <$> (
            (div "case-scrut" <$> (
                op' "case"
                <++> nrty n r (V Blank)
                <++> op' "of"
            )
            <++> (ul' "case-alts" <$> traverse html alts)
        )

instance Html (Alt Meta) where
    html (Alt lhs rhs) = html lhs <++> op "=&gt;" <++> html rhs

instance Html (TT Meta) where
    html (V n) = span "var" <$> html n

    html (I n ty) = span "var instance" <$> html n <++> pure " : " <++> html ty

    html (Bind Pi d tm) =
        span "pi" <$> (
            (parens <$> html d)
            <++> op' " &#8594; "
            <++> html tm
        )

    html (Bind Lam d tm) =
        span "lambda" <$> (
            span "head" <$> (
                op' "&lambda; "
                <++> html d
                <++> op' "."
            )
        )
        <++> html tm

    html (Bind Let d tm) =
        span "let" <$> (
            html d
            <++> pure " in "
            <++> html tm
        )

    html (App r f x) =
        span "app" . parens <$> (
            html f
            <++> pure (app r)
            <++> (erasedSpan r =<< html x)
        )

app :: Meta -> String
app (Fixed R) = span "ap ap-R" "R"
app (Fixed E) = span "ap ap-E" "E"
app (MVar i) = span ("ap mvar-num-" ++ show i) (show i)

erasedSpan :: Meta -> String -> PP String
erasedSpan m body = span <$> erasedCls m <*> pure body

erasedCls :: Meta -> PP String
erasedCls m = do
    uses <- ask
    let erasure
            | m `S.member` uses = "not-erased"
            | otherwise = "erased"
    pure $ erasure ++ " " ++ mvar
  where
    mvar
        | MVar i <- m = "mvar mvar-" ++ show i
        | otherwise = ""

{-
htmlDef :: Uses Meta -> Def Meta -> String
htmlDef(Def n r ty Nothing mcs) = div "def axiom" $ div "type" (nrty n r ty)
htmlDef(Def n r ty (Just tm) mcs) =
  div "def function" (
    div "type" (nrty n r ty)
    ++ div "definition" (
        name n ++ op " = " ++ html tm
    )
  )
-}

htmlConstr :: (Int, (Uses Meta, Guards Meta)) -> String
htmlConstr (i, (us, gs)) = span ("constr constr-" ++ show i) (
    span "uses" (htmlMetas $ S.toList us)
    ++ op " &#8594; "
    ++ span "guards" (htmlMetas $ S.toList gs)
  ) ++ ", "

htmlMetas :: [Meta] -> String
htmlMetas ms = op "{" ++ intercalate (op ", ") (map htmlMeta ms) ++ op "}"

htmlMeta :: Meta -> String
htmlMeta (Fixed R) = span "meta-R" "R"
htmlMeta (Fixed E) = span "meta-E" "E"
htmlMeta (MVar i) = span ("meta mvar mvar-" ++ show i) (show i)

jsConstr :: (Uses Meta, Guards Meta) -> String
jsConstr (us, gs) = show [map num $ S.toList us, map num $ S.toList gs] ++ ",\n"
  where
    num (Fixed r) = show r
    num (MVar i) = show i

genHtml :: String -> Program Meta -> Constrs Meta -> Uses Meta -> IO ()
genHtml fname prog cs uses = do
    hdr <- readFile "html/header.html"
    writeFile fname (hdr ++ body)
  where
    body = unlines
        [ "<h2>Metaified program</h2>"
        , runReader (html prog) uses
        , "<h2>Constraints</h2>"
        , div "constraints" $ concatMap htmlConstr (zip [0..] $ M.toList cs)
        , "<script>var constrs=["
        , concatMap jsConstr (M.toList cs)
        , "[]];</script></body></html>"
        ]
