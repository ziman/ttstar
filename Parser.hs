module Parser (ttProgram) where

import TT
import Data.Char
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
    <|> erasureInstance
    <|> var
    <|> natural
    <?> "atomic expression"

arrow :: Parser (TT MRel)
arrow = (<?> "arrow type") $ do
    ty <- try (atomic <* kwd "->")
    Bind Pi (Def Blank Nothing ty (Abstract Var) noConstrs) <$> expr

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

erasureInstance :: Parser (TT MRel)
erasureInstance = (<?> "erasure instance") $ do
    kwd "["
    n <- name
    kwd ":"
    ty <- expr
    kwd "]"
    return $ I n ty

case_ :: Parser (TT MRel)
case_ = (<?> "case expression") $ do
    kwd "case"
    tm <- parens expr
    kwd "where"
    d <- simpleDef
    return $ Bind Let d tm

expr :: Parser (TT MRel)
expr = 
        case_
    <|> bind
    <|> app
    <?> "expression"  -- app includes nullary-applied atoms

typing :: Abstractness -> Parser (Def MRel)
typing a = (<?> "name binding") $ do
    n <- name
    r <- rcolon
    ty <- expr
    return $ Def n r ty (Abstract a) noConstrs

postulate :: Parser (Def MRel)
postulate = (<?> "postulate") $ do
    kwd "postulate"
    d <- typing Postulate
    kwd "."
    return d

caseTree :: Parser (CaseTree MRel)
caseTree = realCaseTree <|> leaf <?> "case tree or term"

leaf :: Parser (CaseTree MRel)
leaf = Leaf <$> expr

realCaseTree :: Parser (CaseTree MRel)
realCaseTree = (<?> "case tree") $ do
    try $ kwd "case"
    v <- name
    kwd "of"
    alts <- caseAlt `sepBy` kwd ","
    kwd "."
    return $ Case Nothing (V v) alts

caseEq :: Parser (Name, TT MRel)
caseEq = (<?> "case equality") $ do
    kwd "|"
    n <- name
    kwd "="
    tm <- expr
    return (n, tm)

caseLHS :: Parser (AltLHS MRel)
caseLHS = caseLHSCtor <|> (kwd "_" *> pure Wildcard) <?> "case LHS"

caseLHSCtor :: Parser (AltLHS MRel)
caseLHSCtor
    = Ctor Nothing
        <$> name
        <*> many (parens $ typing Var)
        <*> many caseEq
        <?> "constructor case LHS"

caseAlt :: Parser (Alt MRel)
caseAlt
    = Alt
        <$> caseLHS
        <*> (kwd "=>" *> caseTree)
        <?> "constructor-matching case branch"

fundef :: Parser (Def MRel)
fundef = (<?> "function definition") $ do
    n <- name
    args <- many $ parens (typing Var)
    r <- rcolon
    retTy <- expr
    kwd "="

    let ty = chain Pi args retTy

    let lambdaDef = do
            tm <- expr
            kwd "."
            return $ Def n r ty (Term $ chain Lam args tm) noConstrs

    let matchingDef = do
            ct <- realCaseTree  -- `caseTree` allows plain terms but we don't want those here
            -- also, don't require the dot after the case expression because
            -- the case expression knows when to terminate itself
            return $ Def n r ty (Patterns $ CaseFun args ct) noConstrs

    matchingDef <|> lambdaDef
  where
    chain bnd [] tm = tm
    chain bnd (d : args) tm = Bind bnd d $ chain bnd args tm

dataDef :: Parser [Def MRel]
dataDef = (<?> "data definition") $ do
    kwd "data"
    tfd <- typing Postulate
    kwd "."
    ctors <- typing Postulate `sepBy` kwd ","
    kwd "."
    return (tfd : ctors)

simpleDef :: Parser (Def MRel)
simpleDef = postulate <|> fundef <?> "simple definition"

definition :: Parser [Def MRel]
definition = dataDef <|> (pure <$> simpleDef) <?> "definition"

parseProg :: Parser (Program MRel)
parseProg = Prog . concat <$> many definition <?> "program"

ttProgram :: Parser (Program MRel)
ttProgram = sp *> parseProg <* eof
