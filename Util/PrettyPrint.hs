-- This module is equivalent to Text.PrettyPrint.
-- The only difference is slightly different indentation behaviour.
-- (Plus support of code comments).

module Util.PrettyPrint
    ( Doc
    , int, text
    , comma, colon, equals, semicolon, dot
    , lparen, rparen, lbracket, rbracket, lbrace, rbrace
    , (<+>), ($+$), ($$)
    , (<?>)
    , nest
    , parens, brackets, braces
    , empty
    , render
    , vcat, hsep
    , punctuate
    , size, width
    , Pretty (..)
    , showd, printP
    , blankLine
    )
    where

import Data.List
import Data.String

class Pretty a where
    pretty :: a -> Doc

    prettyShow :: a -> String
    prettyShow = render "--" . pretty

printP :: Pretty a => a -> IO ()
printP = putStrLn . prettyShow

type Line = (String, String)  -- text, comment
newtype Doc = Doc [Line]
instance Show Doc where
    show = render "--"

instance IsString Doc where
    fromString = text

infixr 6 <+>
infixr 5 $$, $+$
infixl 1 <?>

blankLine :: Doc
blankLine = text ""

int :: Int -> Doc
int i = text $ show i

text :: String -> Doc
text s = Doc [(s, "")]

comma, colon, semicolon, dot, equals :: Doc
comma     = text ","
colon     = text ":"
semicolon = text ";"
dot       = text "."
equals    = text "="

lparen, rparen, lbracket, rbracket, lbrace, rbrace :: Doc
lparen   = text "("
rparen   = text ")"
lbracket = text "["
rbracket = text "]"
lbrace   = text "{"
rbrace   = text "}"

instance Semigroup Doc where
    Doc xs <> Doc ys = Doc $ meld "" xs ys

(<+>) :: Doc -> Doc -> Doc
Doc xs <+> Doc ys = Doc $ meld " " xs ys

($+$) :: Doc -> Doc -> Doc
Doc xs $+$ Doc ys = Doc $ xs ++ ys

($$) :: Doc -> Doc -> Doc
($$) = ($+$)

-- | Add a comment to the first line of the Doc.
(<?>) :: Doc -> String -> Doc
Doc [] <?> comment = Doc [("", comment)]
Doc ((t,c) : lines) <?> comment = Doc $ (t, merge comment c) : lines
  where
    merge "" y  = y
    merge x  "" = x
    merge x  y  = x ++ " (" ++ y ++ ")"

meld :: String -> [Line] -> [Line] -> [Line]
meld sep [] ys = ys
meld sep xs [] = xs
meld sep [(x,xc)] ((y,yc) : ys) = (x ++ sep ++ y, merge xc yc) : ys
  where
    merge "" y  = y
    merge x  "" = x
    merge x  y  = x ++ ", " ++ y
meld sep (x : xs) ys = x : meld sep xs ys

nest :: Int -> Doc -> Doc
nest n (Doc xs) = Doc [(replicate n ' ' ++ t, c) | (t, c) <- xs]

parens :: Doc -> Doc
parens d = lparen <> d <> rparen

brackets :: Doc -> Doc
brackets d = lbracket <> d <> rbracket

braces :: Doc -> Doc
braces d = lbrace <> d <> rbrace

render :: String -> Doc -> String
render cmtStr (Doc xs) = intercalate "\n" $ map (renderLine cmtStr) xs

renderLine :: String -> (String, String) -> String
renderLine cmtStr ("", "") = ""
renderLine cmtStr ("", comment) = cmtStr ++ " " ++ comment
renderLine cmtStr (content, "") = content
renderLine cmtStr (content, comment) = content ++ "  " ++ cmtStr ++ " " ++ comment

empty :: Doc
empty = Doc []

vcat :: [Doc] -> Doc
vcat = foldr ($+$) empty

hsep :: [Doc] -> Doc
hsep = foldr (<+>) empty

punctuate :: Doc -> [Doc] -> [Doc]
punctuate sep [] = []
punctuate sep [x] = [x]
punctuate sep (x : xs) = (x <> sep) : punctuate sep xs

size :: Doc -> Int
size (Doc xs) = sum [length t | (t, c) <- xs]

width :: Doc -> Int
width (Doc xs) = maximum [length t | (t, c) <- xs]

showd :: Show a => a -> Doc
showd = text . show
