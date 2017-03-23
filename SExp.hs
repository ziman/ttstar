module SExp
    ( SExp(..)
    , SExpable, fromSExp, toSExp
    , parseSExp, dumpSExp, dumpSExpD
    , loadSExp, saveSExp
    ) where

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

    kwd :: Parser ()
    kwd s = (try (string s) *> sp) <?> s

    sv :: Parser SExp
    sv = SV <$> (
            (:)
                (satisfy $ \x -> isIdent x && not (isDigit x))
                (many $ satisfy isIdent)
        ) *> sp <?> "atom"

    ss :: Parser SExp
    ss = SV <$> (kwd "\"" *> many charLit <* kwd "\"")
      where
        charLit =
            (kwd "\\\\" *> return "\\")
            <|> (kwd "\\\"" *> return "\"")
            <|> (kwd "\\n" *> return "\n")
            <|> (return <$> satisfy (/= '"'))

    si :: Parser SExp
    si = SI <$> (read <$> many1 digit) <* sp <?> "integer"

    slist :: Parser SExp
    slist = SL <$> (kwd "(" *> many sexp <* kwd ")")

    sexp :: Parser SExp
    sexp = si <|> ss <|> sv <|> slist <?> "s-expression"


dumpSExpD :: SExp -> Doc
dumpSExpD (SV s)
    | any (\x -> isSpace x || x == '(' || x == ')' || x == '"') s
    = text ("\"" ++ concatMap encodeChar s ++ "\"")

    | otherwise = text s
  where
    encodeChar '"' = "\\\""
    encodeChar '\\' = "\\\\"
    encodeChar '\n' = "\\n"
    encodeChar c = [c]

dumpSExpD (SI i) = text $ show i
dumpSExpD (SL xs) = parens (indent . vcat $ map dumpSExpD xs)

dumpSExp :: SExp -> String
dumpSExp = render "; " . dumpSExpD

loadSExp :: SExpable a => FilePath -> IO (Either String a)
loadSExp fname = (fromSExp =<< parseSExp) <$> readFile fname

saveSExp :: SExpable a => FilePath -> a -> IO ()
saveSExp fname = writeFile fname . dumpSExp . toSExp
