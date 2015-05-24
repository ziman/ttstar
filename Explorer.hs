module Explorer (genHtml) where

import TT

import Erasure.Meta
import Erasure.Check
import Erasure.Solve

import Data.List (intercalate)
import Prelude hiding (div, span)
import qualified Data.Set as S
import qualified Data.Map as M

htmlProg :: Uses -> Program Meta cs -> String
htmlProg uses (Prog defs) = concatMap (htmlDef uses) defs

div :: String -> String -> String
div cls body = "<div class=\"" ++ cls ++ "\">\n" ++ body ++ "\n</div>\n"

span :: String -> String -> String
span cls body = "<span class=\"" ++ cls ++ "\">" ++ body ++ "</span>"

rel :: Uses -> Meta -> String
rel uses (Fixed R) = span "rel rel-R" " :<sub>R</sub> "
rel uses (Fixed E) = span "rel rel-E" " :<sub>E</sub> "
rel uses (MVar i j) = span ("rel mvar-num-" ++ mv i j) (" :<sub>" ++ mv i j ++ "</sub> ")

link :: String -> String -> String
link cls body = "<a class=\"" ++ cls ++ "\" href=\"#\">" ++ body ++ "</a>"

name :: Name -> String
name n = span ("name name-" ++ n) n

op :: String -> String
op = span "op"

mv :: Int -> Int -> String
mv i 0 = show i
mv i j = show i ++ "_" ++ show j

nrty :: Uses -> Name -> Meta -> TT Meta -> String
nrty uses n r ty = erasedSpan uses r (name n ++ rel uses r ++ term uses ty ++ "\n")
  where
    wrap
        | Fixed _ <- r = span ("nrty " ++ cls)
        | MVar i j <- r = span ("nrty nrty-" ++ mv i j ++ " " ++ cls)

    cls | r `S.member` uses = "nrty-R"
        | otherwise = "nrty-E erased"

parens :: String -> String
parens s = span "paren" "(" ++ s ++ span "paren" ")"

ul :: String -> [String] -> String
ul cls lis = "<ul class=\"" ++ cls ++ "\">" ++ unlines ["<li>" ++ s ++ "</li>" | s <- lis] ++ "</ul>"

term :: Uses -> TT Meta -> String
term uses (V n) = span "var" $ name n
term uses (Bind Pi n r ty tm) = span "pi" $ parens (nrty uses n r ty) ++ op " &#8594; " ++ term uses tm
term uses (Bind Lam n r ty tm) = span "lambda" $ span "head" (op "&lambda; " ++ nrty uses n r ty ++ op ".") ++ term uses tm
term uses (App r f x) = span "app" . parens $ term uses f ++ app r ++ erasedSpan uses r (term uses x)
term uses Type = span "star" "*"
term uses Erased = span "erased" "____"
term uses (Case s alts) =
  span "kwd" "case" ++ " " ++ term uses s ++ " " ++ span "kwd" "of"
  ++ ul "case" (map (alt uses) alts)

alt :: Uses -> Alt Meta -> String
alt uses (DefaultCase tm) = "_ -> " ++ term uses tm
alt uses (ConCase cn tm) = unwords
    [ cn
    , unwords $ map (\(n,r,ty) -> parens $ nrty uses n r ty) args
    , "->"
    , term uses rhs
    ]
  where
    (args, rhs) = splitBinder Pat tm

app :: Meta -> String
app (Fixed R) = span "ap ap-R" "R"
app (Fixed E) = span "ap ap-E" "E"
app (MVar i j) = span ("ap mvar-num-" ++ mv i j) (mv i j)

erasedSpan :: Uses -> Meta -> String -> String
erasedSpan uses m = span $ erasedCls uses m

erasedCls :: Uses -> Meta -> String
erasedCls uses m = erasure ++ " " ++ mvar
  where
    erasure
        | m `S.member` uses = "not-erased"
        | otherwise = "erased"

    mvar
        | MVar i j <- m = "mvar mvar-" ++ mv i j
        | otherwise = ""

htmlDef :: Uses -> Def Meta cs -> String
htmlDef uses (Def n r ty Nothing mcs) = div "def axiom" $ div "type" (nrty uses n r ty)
htmlDef uses (Def n r ty (Just tm) mcs) =
  div "def function" (
    div "type" (nrty uses n r ty)
    ++ div "definition" (
        name n ++ op " = " ++ term uses tm
    )
  )

htmlConstr :: (Int, (Uses, Guards)) -> String
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
htmlMeta (MVar i j) = span ("meta mvar mvar-" ++ mv i j) (mv i j)

jsConstr :: (Uses, Guards) -> String
jsConstr (us, gs) = show [map num $ S.toList us, map num $ S.toList gs] ++ ",\n"
  where
    num (Fixed r) = show r
    num (MVar i j) = mv i j

genHtml :: String -> Program Meta cs -> Constrs -> Uses -> IO ()
genHtml fname prog cs uses = do
    hdr <- readFile "html/header.html"
    writeFile fname (hdr ++ body)
  where
    body = unlines
        [ "<h2>Metaified program</h2>"
        , htmlProg uses prog
        , "<h2>Constraints</h2>"
        , div "constraints" $ concatMap htmlConstr (zip [0..] $ M.toList cs)
        , "<script>var constrs=["
        , concatMap jsConstr (M.toList cs)
        , "[]];</script></body></html>"
        ]
