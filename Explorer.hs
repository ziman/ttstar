module Explorer (genHtml) where

import TT

import Erasure.Meta
import Erasure.Check

import Prelude hiding (div, span)
import qualified Data.Set as S

htmlProg :: Uses -> Program Meta -> String
htmlProg uses (Prog defs) = concatMap (htmlDef uses) defs

div :: String -> String -> String
div cls body = "<div class=\"" ++ cls ++ "\">\n" ++ body ++ "\n</div>\n"

span :: String -> String -> String
span cls body = "<span class=\"" ++ cls ++ "\">" ++ body ++ "</span>"

rel :: Uses -> Meta -> String
rel uses (Fixed R) = span "rel rel-R" " :<sub>R</sub> "
rel uses (Fixed I) = span "rel rel-I" " :<sub>I</sub> "
rel uses (MVar i) = link ("rel mvar-" ++ show i ++ " " ++ cls) (" :<sub>" ++ show i ++ "</sub> ")
  where
    cls | MVar i `S.member` uses = "rel-R"
        | otherwise = "rel-I"

link :: String -> String -> String
link cls body = "<a class=\"" ++ cls ++ "\" href=\"#\">" ++ body ++ "</a>"

name :: Name -> String
name n = span ("name name-" ++ n) n

op :: String -> String
op = span "op"

nrty :: Uses -> Name -> Meta -> TT Meta -> String
nrty uses n r ty = wrap (name n ++ rel uses r ++ term uses ty ++ "\n")
  where
    wrap
        | Fixed _ <- r = span ("nrty " ++ cls)
        | MVar  i <- r = span ("nrty nrty-" ++ show i ++ " " ++ cls)

    cls | r `S.member` uses = "nrty-R"
        | otherwise = "nrty-I"

parens :: String -> String
parens s = span "paren" "(" ++ s ++ span "paren" ")"

term :: Uses -> TT Meta -> String
term uses (V n) = span "var" $ name n
term uses (Bind Pi r n ty tm) = span "pi" $ parens (nrty uses n r ty) ++ op " &#8594; " ++ term uses tm
term uses (Bind Lam r n ty tm) = span "lambda" $ span "head" (op "&lambda; " ++ nrty uses n r ty ++ op ".") ++ term uses tm
term uses (App r f x) = span "app" . parens $ term uses f ++ " " ++ term uses x
term uses (Case s alts) = error "not implemented"
term uses Type = span "star" "*"
term uses Erased = span "erased" "____"

htmlDef :: Uses -> Def Meta -> String
htmlDef uses (Def r n ty Axiom) = div "def axiom" $ div "type" (nrty uses n r ty)
htmlDef uses (Def r n ty (Fun tm)) =
  div "def function" (
    div "type" (nrty uses n r ty)
    ++ div "definition" (
        name n ++ op " = " ++ term uses tm
    )
  )

genHtml :: String -> Program Meta -> Constrs -> Uses -> IO ()
genHtml fname prog cs uses = do
    hdr <- readFile "html/header.html"
    ftr <- readFile "html/footer.html"
    writeFile fname (hdr ++ body ++ ftr)
  where
    body = htmlProg uses prog
