module Explorer (genHtml) where

import TT

import Erasure.Evar
import Erasure.Check
import Erasure.Solve

import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import Prelude hiding (div, span)
import qualified Data.Set as S
import qualified Data.Map as M

htmlProg :: Uses -> Program Evar cs -> String
htmlProg uses (Prog defs) = concatMap (htmlDef uses) defs

div :: String -> String -> String
div cls body = "<div class=\"" ++ cls ++ "\">\n" ++ body ++ "\n</div>\n"

span :: String -> String -> String
span cls body = "<span class=\"" ++ cls ++ "\">" ++ body ++ "</span>"

rel :: Uses -> Evar -> String
rel uses (Fixed R) = span "rel rel-R" " :<sub>R</sub> "
rel uses (Fixed E) = span "rel rel-E" " :<sub>E</sub> "
rel uses (MVar i) = span ("rel mvar-num-" ++ show i) (" :<sub>" ++ show i ++ "</sub> ")

link :: String -> String -> String
link cls body = "<a class=\"" ++ cls ++ "\" href=\"#\">" ++ body ++ "</a>"

name :: Name -> String
name n = span ("name name-" ++ show n) (show n)

op :: String -> String
op = span "op"

nrty :: Uses -> Name -> Evar -> TT Evar -> String
nrty uses n r ty = erasedSpan uses r (name n ++ rel uses r ++ term uses ty ++ "\n")
  where
    wrap
        | Fixed _ <- r = span ("nrty " ++ cls)
        | MVar i <- r = span ("nrty nrty-" ++ show i ++ " " ++ cls)

    cls | r `S.member` uses = "nrty-R"
        | otherwise = "nrty-E erased"

parens :: String -> String
parens s = span "paren" "(" ++ s ++ span "paren" ")"

ul :: String -> [String] -> String
ul cls lis = "<ul class=\"" ++ cls ++ "\">" ++ unlines ["<li>" ++ s ++ "</li>" | s <- lis] ++ "</ul>"

term :: Uses -> TT Evar -> String
term uses (V n) = span "var" $ name n
term uses (I n ty) = span "var instance" $ name n ++ " : " ++ term uses ty
term uses (Bind Pi n r ty tm) = span "pi" $ parens (nrty uses n r ty) ++ op " &#8594; " ++ term uses tm
term uses (Bind Lam n r ty tm) = span "lambda" $ span "head" (op "&lambda; " ++ nrty uses n r ty ++ op ".") ++ term uses tm
term uses (Let (Def n r ty mtm Nothing) tm) =
    span "let" $ nrty uses n r ty ++ " = " ++ term uses (fromMaybe Erased mtm) ++ " in " ++ term uses tm
term uses (App r f x) = span "app" . parens $ term uses f ++ app r ++ erasedSpan uses r (term uses x)
term uses Type = span "star" "*"
term uses Erased = span "erased" "____"
term uses (Case s ty alts) =
    span "kwd" "case" ++ " " ++ term uses s ++ " " ++ ret ty ++ span "kwd" "of"
    ++ ul "case" (map (alt uses) alts)
  where
    ret Nothing = ""
    ret (Just ty) = span "kwd" "returns" ++ term uses ty

alt :: Uses -> Alt Evar -> String
alt uses (DefaultCase tm) = "_ -> " ++ term uses tm
alt uses (ConCase cn tm) = unwords
    [ show cn
    , unwords $ map (\(n,r,ty) -> parens $ nrty uses n r ty) args
    , "->"
    , term uses rhs
    ]
  where
    (args, rhs) = splitBinder Pat tm

app :: Evar -> String
app (Fixed R) = span "ap ap-R" "R"
app (Fixed E) = span "ap ap-E" "E"
app (MVar i) = span ("ap mvar-num-" ++ show i) (show i)

erasedSpan :: Uses -> Evar -> String -> String
erasedSpan uses m = span $ erasedCls uses m

erasedCls :: Uses -> Evar -> String
erasedCls uses m = erasure ++ " " ++ mvar
  where
    erasure
        | m `S.member` uses = "not-erased"
        | otherwise = "erased"

    mvar
        | MVar i <- m = "mvar mvar-" ++ show i
        | otherwise = ""

htmlDef :: Uses -> Def Evar cs -> String
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
    span "uses" (htmlEvars $ S.toList us)
    ++ op " &#8594; "
    ++ span "guards" (htmlEvars $ S.toList gs)
  ) ++ ", "

htmlEvars :: [Evar] -> String
htmlEvars ms = op "{" ++ intercalate (op ", ") (map htmlEvar ms) ++ op "}"

htmlEvar :: Evar -> String
htmlEvar (Fixed R) = span "evar-R" "R"
htmlEvar (Fixed E) = span "evar-E" "E"
htmlEvar (MVar i) = span ("evar mvar mvar-" ++ show i) (show i)

jsConstr :: (Uses, Guards) -> String
jsConstr (us, gs) = show [map num $ S.toList us, map num $ S.toList gs] ++ ",\n"
  where
    num (Fixed r) = show r
    num (MVar i) = show i

genHtml :: String -> Program Evar cs -> Constrs -> Uses -> IO ()
genHtml fname prog (CS cs) uses = do
    hdr <- readFile "html/header.html"
    writeFile fname (hdr ++ body)
  where
    body = unlines
        [ "<h2>Evarified program</h2>"
        , htmlProg uses prog
        , "<h2>Constraints</h2>"
        , div "constraints" $ concatMap htmlConstr (zip [0..] $ M.toList cs)
        , "<script>var constrs=["
        , concatMap jsConstr (M.toList cs)
        , "[]];</script></body></html>"
        ]
