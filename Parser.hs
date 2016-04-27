module Parser (ttProgram) where

import TT

import Data.Char

import Control.Applicative hiding (many, (<|>))
import Control.Monad

import Text.Parsec

type Parser = Parsec String ()
type MRel = Maybe Relevance

lineComment :: Parser ()
lineComment = kwd "--" *> many (satisfy (/= '\n')) *> return () <?> "line comment"

bigComment :: Parser ()
bigComment = kwd "{-" *> manyTill anyChar (try $ kwd "-}") *> return () <?> "block comment"

sp :: Parser ()
sp = many ((satisfy isSpace *> return ()) <|> lineComment <|> bigComment) *> return () <?> "whitespace or comment"

kwd :: String -> Parser ()
kwd s = (try (string s) >> sp) <?> s

name :: Parser Name
name = (<?> "name") $ do
    x <- satisfy idChar
    xs <- many $ satisfy (\x -> idChar x || isDigit x)
    sp
    return $ UN (x : xs)
  where
    idChar x = isAlpha x || x `elem` "_"

rcolon :: Parser MRel
rcolon =
        (kwd ":R:" *> pure (Just R))
    <|> (kwd ":E:" *> pure (Just E))
    <|> (kwd  ":"  *> pure (Nothing))
    <?> "colon"

parens :: Parser a -> Parser a
parens = between (kwd "(") (kwd ")")

var :: Parser (TT MRel)
var = V <$> name <?> "variable"

natural :: Parser (TT MRel)
natural = mkNat . read <$> (many1 (satisfy isDigit) <* sp) <?> "number"
  where
    mkNat :: Int -> TT MRel
    mkNat 0 = V $ UN "Z"
    mkNat k = App Nothing (V $ UN "S") (mkNat (k-1))

atomic :: Parser (TT MRel)
atomic = parens expr
    <|> instOrForced
    <|> var
    <|> (kwd "*" *> pure Type)
    <|> natural
    <?> "atomic expression"

arrow :: Parser (TT MRel)
arrow = (<?> "arrow type") $ do
    ty <- try (atomic <* kwd "->")
    Bind Pi (Def (UN "_") Nothing ty Abstract Nothing) <$> expr

lambda :: Parser (TT MRel)
lambda = (<?> "lambda") $ do
    kwd "\\"
    d <- typing
    kwd "."
    Bind Lam d <$> expr

bpi :: Parser (TT MRel)
bpi = (<?> "pi") $ do
    d <- try $ parens typing
    kwd "->"
    Bind Pi d <$> expr

bind :: Parser (TT MRel)
bind = arrow
    <|> lambda
    <|> bpi
    <|> let_
    <?> "binder"

app :: Parser (TT MRel)
app = foldl (App Nothing) <$> atomic <*> many atomic <?> "application"

let_ :: Parser (TT MRel)
let_ = (<?> "let expression") $ do
    kwd "let"
    kwd "("
    Def n r ty Abstract Nothing <- typing
    kwd "="
    body <- Term <$> expr
    kwd ")"
    kwd "in"
    Bind Let (Def n r ty body Nothing) <$> expr

instOrForced :: Parser (TT MRel)
instOrForced = kwd "[" >> (try inst <|> forced)

inst :: Parser (TT MRel)
inst = (<?> "erasure instance") $ do
    n <- name
    kwd ":"
    ty <- expr
    kwd "]"
    return $ I n ty

forced :: Parser (TT MRel)
forced = (<?> "forced pattern") $ do
    tm <- expr
    kwd "]"
    return $ Forced tm

expr :: Parser (TT MRel)
expr =  bind
    <|> app
    <?> "expression"  -- app includes nullary-applied atoms

typing :: Parser (Def MRel VoidConstrs)
typing = (<?> "name binding") $ do
    n <- name
    r <- rcolon
    ty <- expr
    return $ Def n r ty Abstract Nothing

postulate :: Parser (Def MRel VoidConstrs)
postulate = kwd "postulate" *> typing <* kwd "." <?> "postulate"

patvars :: Parser [Def MRel VoidConstrs]
patvars = (<?> "pattern variables") $ do
    kwd "pat"
    pvs <- many (parens typing)
    kwd "."
    return pvs

clause :: Parser (Clause MRel)
clause = (<?> "clause") $ do
    pvs <- patvars <|> return []
    lhs <- expr
    kwd "="
    rhs <- expr
    return $ Clause pvs lhs rhs

fundef :: Parser (Def MRel VoidConstrs)
fundef = (<?> "function definition") $ do
    Def n r ty Abstract Nothing <- typing
    kwd "."
    cls <- clause `sepBy` kwd ","
    kwd "."
    return $ Def n r ty (Clauses cls) Nothing

parseDef :: Parser (Def MRel VoidConstrs)
parseDef = postulate <|> fundef <?> "definition"

parseProg :: Parser (Program MRel VoidConstrs)
parseProg = Prog <$> many parseDef <?> "program"

ttProgram :: Parser (Program MRel VoidConstrs)
ttProgram = sp *> parseProg <* eof
