module Parser (parseProgram) where

import TT
import Data.Char
import Text.Parsec
import qualified Data.Map as M
import qualified Data.Set as S

data ParserState = PS
    { psCounters :: M.Map String Int
    }
    deriving (Eq, Ord, Show)

type Parser = Parsec String ParserState
type MRel = Maybe Relevance

parseProgram :: String -> String -> Either ParseError (Program MRel)
parseProgram fname body = runParser ttProgram initialParserState fname body

initialParserState :: ParserState
initialParserState = PS
    { psCounters = M.empty
    }

freshMN :: String -> Parser Name
freshMN stem = do
    st <- getState
    let cs = psCounters st
    let i = M.findWithDefault 0 stem cs
    putState st{ psCounters = M.insert stem (i+1) cs }
    return $ MN stem i

keywords :: S.Set String
keywords = S.fromList [
    "case", "with", "where",
    "data", "let", "in", "postulate",
    "of"
  ]

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
    n <- try $ do
        x <- satisfy isAlpha  -- let's make _idents reserved for the compiler
        xs <- many $ satisfy (\x -> idChar x || isDigit x)
        let n = x:xs
        if S.member n keywords
            then unexpected n
            else return n
    sp
    return $ UN n
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
    n <- freshMN "x"
    ty <- try (atomic <* kwd "->")
    Bind Pi [Def n Nothing ty (Abstract Var) noConstrs] <$> expr

lambda :: Parser (TT MRel)
lambda = (<?> "lambda") $ do
    kwd "\\"
    d <- typing Var
    kwd "."
    Bind Lam [d] <$> expr

bpi :: Parser (TT MRel)
bpi = (<?> "pi") $ do
    d <- try $ parens (typing Var)
    kwd "->"
    Bind Pi [d] <$> expr

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
    ds <- many (kwd "," *> simpleDef)
    kwd "in"
    Bind Let (d:ds) <$> expr

erasureInstance :: Parser (TT MRel)
erasureInstance = (<?> "erasure instance") $ do
    kwd "["
    n <- name
    kwd ":"
    ty <- expr
    kwd "]"
    return $ I n ty

caseExpr :: Parser (TT MRel)
caseExpr = (<?> "case expression") $ do
    n <- freshMN "casefun"
    kwd "case"
    tm <- expr
    kwd "where"
    ty <- expr
    kwd "."
    alts <- caseAlt `sepBy` kwd ","
    case mkArgs ty of
        arg:_ -> do
            let cf = CaseFun [arg] (Case Nothing (V $ defName arg) alts)
            return $
                Bind Let
                    [Def n Nothing ty (Patterns cf) noConstrs]
                        (App Nothing (V n) tm)
        args -> fail "case function must take at least one argument"
  where
    mkArgs (Bind Pi ds tm) = ds ++ mkArgs tm
    mkArgs _ = []

expr :: Parser (TT MRel)
expr = 
        caseExpr
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
    kwd "{"
    alts <- caseAlt `sepBy` kwd ","
    kwd "}"
    return $ Case Nothing (V v) alts

altLHS :: Parser (AltLHS MRel)
altLHS =
  (altLHSForced <?> "forced alt LHS")
  <|> (altLHSCtor <?> "constructor alt LHS")
  <|> (kwd "_" *> pure Wildcard)
  <?> "case alt LHS"

altLHSForced :: Parser (AltLHS MRel)
altLHSForced = do
    kwd "["
    tm <- expr
    kwd "]"
    ds <- many (parens $ typing Var)
    case (tm, ds) of
        (_   , []) -> return $ ForcedPat tm
        (V cn, _ ) -> return $ Ctor (CTForced cn) ds
        _ -> fail "weird forced alt LHS"

altLHSCtor :: Parser (AltLHS MRel)
altLHSCtor
    = Ctor
        <$> (CT <$> name <*> pure Nothing)
        <*> many (parens $ typing Var)

caseAlt :: Parser (Alt MRel)
caseAlt
    = Alt
        <$> Parser.altLHS
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
            return $ Def n r ty (Term $ chain Lam args tm) noConstrs

    let matchingDef = do
            ct <- realCaseTree  -- `caseTree` allows plain terms but we don't want those here
            -- also, don't require the dot after the case expression because
            -- the case expression knows when to terminate itself
            return $ Def n r ty (Patterns $ CaseFun args ct) noConstrs

    matchingDef <|> lambdaDef
  where
    chain bnd [] tm = tm
    chain bnd (d : args) tm = Bind bnd [d] $ chain bnd args tm

dataDef :: Parser [Def MRel]
dataDef = (<?> "data definition") $ do
    kwd "data"
    tfd <- typing Postulate
    kwd "where"
    ctors <- typing Postulate `sepBy` kwd ","
    return (tfd : ctors)

simpleDef :: Parser (Def MRel)
simpleDef = postulate <|> fundef <?> "simple definition"

definition :: Parser [Def MRel]
definition = dataDef <|> (pure <$> simpleDef) <?> "definition"

parseProg :: Parser (Program MRel)
parseProg = do
    ds <- concat <$> many (definition <* optional (kwd ".")) <?> "program"
    return $ Bind Let ds (V $ UN "main")

ttProgram :: Parser (Program MRel)
ttProgram = sp *> parseProg <* eof
