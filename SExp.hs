module SExp
    ( SExp(..)
    , SExpable, fromSExp, toSExp
    , parseSExp, dumpSExp, dumpSExpD
    , loadSExp, saveSExp
    ) where

import Data.Char
import Control.Monad
import Text.Parsec
import Util.PrettyPrint hiding ((<?>))

data SExp
    = SV String
    | SI Int
    | SL [SExp]
    deriving (Eq, Ord, Show)

class SExpable a where
    fromSExp :: SExp -> Either String a
    toSExp :: a -> SExp

type Parser = Parsec String ()

isIdent :: Char -> Bool
isIdent x = not (isSpace x || x == '(' || x == ')' || x == '"')

parseSExp :: String -> Either String SExp
parseSExp content =
    case runParser sexp () "s-expression" content of
        Left err -> Left (show err)
        Right e  -> Right e
  where
    sp :: Parser ()
    sp = many (satisfy isSpace) *> return () <?> "whitespace"

    kwd :: String -> Parser ()
    kwd s = (try (string s) *> sp) <?> s

    sv :: Parser SExp
    sv = SV <$> (
            (:)
                <$> (satisfy $ \x -> isIdent x && not (isDigit x))
                <*> (many $ satisfy isIdent)
        ) <* sp <?> "atom"

    ss :: Parser SExp
    ss = SV <$> (kwd "\"" *> many charLit <* kwd "\"")
      where
        charLit :: Parser Char
        charLit =
            (kwd "\\\\" *> return '\\')
            <|> (kwd "\\\"" *> return '\"')
            <|> (kwd "\\n" *> return '\n')
            <|> (satisfy (/= '"'))

    si :: Parser SExp
    si = SI <$> (read <$> many1 digit) <* sp <?> "integer"

    slist :: Parser SExp
    slist = SL <$> (kwd "(" *> many sexp <* kwd ")")

    sexp :: Parser SExp
    sexp = si <|> ss <|> sv <|> slist <?> "s-expression"


-- returns:
-- 1. the document
-- 2. size of the document
dumpSExpD :: SExp -> (Doc, Int)
dumpSExpD (SV s)
    | any (\x -> isSpace x || x == '(' || x == ')' || x == '"') s
    = 
        let doc = text ("\"" ++ concatMap encodeChar s ++ "\"")
          in (doc, size doc)

    | otherwise = (text s, length s)
  where
    encodeChar '"' = "\\\""
    encodeChar '\\' = "\\\\"
    encodeChar '\n' = "\\n"
    encodeChar c = [c]

dumpSExpD (SI i) = (text $ show i, length $ show i)

dumpSExpD (SL xs)
    | subSize >= 50 = (multiLine,  subSize)
    | otherwise     = (singleLine, subSize)
  where
    subs = map dumpSExpD xs
    subDocs = map fst subs
    subSize = sum $ map snd subs

    singleLine = parens (hsep subDocs)
    multiLine = case subDocs of
        []   -> parens empty
        d:ds -> parens (d $$ nest 2 (vcat ds))

dumpSExp :: SExp -> String
dumpSExp = render "; " . fst . dumpSExpD

loadSExp :: SExpable a => FilePath -> IO (Either String a)
loadSExp fname = (fromSExp <=< parseSExp) <$> readFile fname

saveSExp :: SExpable a => FilePath -> a -> IO ()
saveSExp fname = writeFile fname . dumpSExp . toSExp
