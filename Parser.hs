module Parser where

import TTstar

import Data.Char

import Control.Applicative hiding (many, (<|>))
import Control.Monad

import Text.Parsec

type Parser = Parsec String ()

lineComment :: Parser ()
lineComment = kwd "--" >> many (satisfy (/= '\n')) >> return ()

bigComment :: Parser ()
bigComment = kwd "{-" >> manyTill anyChar (try $ kwd "-}") >> return ()

sp :: Parser ()
sp = many ((satisfy isSpace *> return ()) <|> lineComment <|> bigComment) >> return ()

kwd :: String -> Parser ()
kwd s = try (string s) >> sp

name :: Parser Name
name = do
    x <- satisfy $ idChar
    xs <- many $ satisfy (\x -> idChar x || isDigit x)
    sp
    return (x : xs)
  where
    idChar x = isAlpha x || x `elem` "_"

rcolon :: Parser MRel
rcolon =
        (kwd ":R:" *> pure (Just R))
    <|> (kwd ":I:" *> pure (Just I))
    <|> (kwd  ":"  *> pure (Nothing))

parens :: Parser a -> Parser a
parens = between (kwd "(") (kwd ")")

var :: Parser (TT MRel)
var = V <$> name

natural :: Parser (TT MRel)
natural = mkNat . read <$> (many1 (satisfy isDigit) <* sp)
  where
    mkNat :: Int -> TT MRel
    mkNat 0 = V "Z"
    mkNat k = App Nothing (V "S") (mkNat (k-1))

atomic :: Parser (TT MRel)
atomic = parens expr
    <|> var
    <|> (kwd "*" *> pure Type)
    <|> natural

arrow :: Parser (TT MRel)
arrow = do
    ty <- try (atomic <* kwd "->")
    Bind Pi Nothing "_" ty <$> expr

lambda :: Parser (TT MRel)
lambda = do
    kwd "\\"
    (n, r, ty) <- typing
    kwd "."
    Bind Lam r n ty <$> expr

bpi :: Parser (TT MRel)
bpi = do
    (n, r, ty) <- parens typing
    kwd "->"
    Bind Pi r n ty <$> expr  

bind :: Parser (TT MRel)
bind = arrow
    <|> lambda
    <|> bpi

app :: Parser (TT MRel)
app = mkApp <$> atomic <*> many atomic
  where
    mkApp f [] = f
    mkApp f (x : xs) = mkApp (App Nothing f x) xs

expr :: Parser (TT MRel)
expr = bind <|> app  -- app includes nullary-applied atoms

typing :: Parser (Name, MRel, TT MRel)
typing = do
    n <- name
    r <- rcolon
    ty <- expr
    return (n, r, ty)

postulate :: Parser (Def MRel)
postulate = do
    kwd "postulate"
    (n, r, ty) <- typing
    kwd "."
    return $ Def r n ty Axiom

fundef :: Parser (Def MRel)
fundef = do
    (n, r, ty) <- typing
    kwd "="
    tm <- expr
    kwd "."
    return $ Def r n ty (Fun tm)

parseDef :: Parser (Def MRel)
parseDef = postulate <|> fundef

parseProg :: Parser (Program MRel)
parseProg = Prog <$> many parseDef
