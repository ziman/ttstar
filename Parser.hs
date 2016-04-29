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
    idChar x = isAlpha x || x `elem` "_'"

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
    <|> natural
    <?> "atomic expression"

arrow :: Parser (TT MRel)
arrow = (<?> "arrow type") $ do
    ty <- try (atomic <* kwd "->")
    Bind Pi (Def Blank Nothing ty (Abstract Var) Nothing) <$> expr

lambda :: Parser (TT MRel)
lambda = (<?> "lambda") $ do
    kwd "\\"
    d <- typing Var
    kwd "."
    Bind Lam d <$> expr

bpi :: Parser (TT MRel)
bpi = (<?> "pi") $ do
    d <- try $ parens (typing Var)
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
    d <- simpleDef
    kwd "in"
    Bind Let d <$> expr

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

typing :: Abstractness -> Parser (Def MRel VoidConstrs)
typing a = (<?> "name binding") $ do
    n <- name
    r <- rcolon
    ty <- expr
    return $ Def n r ty (Abstract a) Nothing

postulate :: Parser (Def MRel VoidConstrs)
postulate = (<?> "postulate") $ do
    kwd "postulate"
    d <- typing Postulate
    kwd "."
    return d

mkPostulate :: Def MRel VoidConstrs -> Def MRel VoidConstrs
mkPostulate (Def n r ty (Abstract Var) Nothing) = Def n r ty (Abstract Postulate) Nothing

patvars :: Parser [Def MRel VoidConstrs]
patvars = (<?> "pattern variables") $ do
    kwd "pat"
    pvs <- many (parens $ typing Var)
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
    -- we try typing because it may be a mldef
    Def n r ty (Abstract Var) Nothing <- try (typing Var <* kwd ".")
    cls <- clause `sepBy` kwd ","
    kwd "."
    return $ Def n r ty (Clauses cls) Nothing

mldef :: Parser (Def MRel VoidConstrs)
mldef = (<?> "ml-style definition") $ do
    n <- name
    args <- many $ parens (typing Var)
    r <- rcolon
    retTy <- expr
    kwd "="
    tm <- expr
    kwd "."
    return $ Def n r (chain Pi args retTy) (Term $ chain Lam args tm) Nothing
  where
    chain bnd [] tm = tm
    chain bnd (d : args) tm = Bind bnd d $ chain bnd args tm

dataDef :: Parser [Def MRel VoidConstrs]
dataDef = (<?> "data definition") $ do
    kwd "data"
    tfd <- typing Postulate
    kwd "."
    ctors <- typing Postulate `sepBy` kwd ","
    kwd "."
    return (tfd : ctors)

simpleDef :: Parser (Def MRel VoidConstrs)
simpleDef = postulate <|> fundef <|> mldef <?> "simple definition"

definition :: Parser [Def MRel VoidConstrs]
definition = dataDef <|> (pure <$> simpleDef) <?> "definition"

parseProg :: Parser (Program MRel VoidConstrs)
parseProg = Prog . concat <$> many definition <?> "program"

ttProgram :: Parser (Program MRel VoidConstrs)
ttProgram = sp *> parseProg <* eof
