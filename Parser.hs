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
    x <- satisfy $ idChar
    xs <- many $ satisfy (\x -> idChar x || isDigit x)
    sp
    return (x : xs)
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
    mkNat 0 = V "Z"
    mkNat k = App Nothing (V "S") (mkNat (k-1))

atomic :: Parser (TT MRel)
atomic = parens expr
    <|> var
    <|> (kwd "*" *> pure Type)
    <|> natural
    <?> "atomic expression"

arrow :: Parser (TT MRel)
arrow = (<?> "arrow type") $ do
    ty <- try (atomic <* kwd "->")
    Bind Pi "_" Nothing ty <$> expr

lambda :: Parser (TT MRel)
lambda = (<?> "lambda") $ do
    kwd "\\"
    (n, r, ty) <- typing
    kwd "."
    Bind Lam n r ty <$> expr

bpi :: Parser (TT MRel)
bpi = (<?> "pi") $ do
    (n, r, ty) <- parens typing
    kwd "->"
    Bind Pi n r ty <$> expr  

bind :: Parser (TT MRel)
bind = arrow
    <|> lambda
    <|> bpi
    <?> "binder"

app :: Parser (TT MRel)
app = mkApp <$> atomic <*> many atomic <?> "application"
  where
    mkApp f [] = f
    mkApp f (x : xs) = mkApp (App Nothing f x) xs

expr :: Parser (TT MRel)
expr = case_ <|> bind <|> app <?> "expression"  -- app includes nullary-applied atoms

case_ :: Parser (TT MRel)
case_ = (<?> "case") $ do
    kwd "case" 
    s <- parens expr
    kwd "of"
    alts <- alt `sepBy` kwd ","
    return $ Case s alts

alt :: Parser (Alt MRel)
alt = defaultCase <|> conCase <?> "case alt"

defaultCase :: Parser (Alt MRel)
defaultCase = (<?> "default case") $ do
    kwd "_"
    kwd "->"
    DefaultCase <$> expr

conCase :: Parser (Alt MRel)
conCase = (<?> "constr case") $ do
    cn <- name
    ns <- many $ parens typing
    kwd "->"
    rhs <- expr
    return $ ConCase cn (tack ns rhs)
  where
    tack [] tm = tm
    tack ((n,r,ty) : ns) tm = Bind Pat n r ty $ tack ns tm

typing :: Parser (Name, MRel, TT MRel)
typing = (<?> "typing") $ do
    n <- name
    r <- rcolon
    ty <- expr
    return (n, r, ty)

postulate :: Parser (Def MRel Void)
postulate = (<?> "postulate") $ do
    kwd "postulate"
    (n, r, ty) <- typing
    kwd "."
    return $ Def n r ty Nothing Nothing

mldef :: Parser (Def MRel Void)
mldef = (<?> "ml-style definition") $ do
    n <- name
    args <- many $ parens typing
    r <- rcolon
    retTy <- expr
    kwd "="
    tm <- expr
    kwd "."
    return $ Def n r (chain Pi args retTy) (Just $ chain Lam args tm) Nothing
  where
    chain bnd [] tm = tm
    chain bnd ((n, r, ty) : args) tm = Bind bnd n r ty $ chain bnd args tm
    
fundef :: Parser (Def MRel Void)
fundef = (<?> "function definition") $ do
    (n, r, ty) <- try typing
    kwd "="
    tm <- expr
    kwd "."
    return $ Def n r ty (Just tm) Nothing

parseDef :: Parser (Def MRel Void)
parseDef = postulate <|> fundef <|> mldef <?> "definition"

parseProg :: Parser (Program MRel Void)
parseProg = Prog <$> many parseDef <?> "program"

ttProgram :: Parser (Program MRel Void)
ttProgram = sp *> parseProg <* eof
