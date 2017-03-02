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
    -- <|> caseExpr
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

brackets :: Parser a -> Parser a
brackets p = kwd "[" *> p <* kwd "]"

patVar :: Parser (Pat MRel)
patVar = PV <$> name <?> "pattern variable"

patForced :: Parser (Pat MRel)
patForced = PForced <$> brackets expr <?> "forced pattern"

patAtom :: Parser (Pat MRel)
patAtom = parens pattern <|> patForced <|> patVar <?> "pattern atom"

patApp :: Parser (Pat MRel)
patApp = foldl (PApp Nothing) <$> patAtom <*> many patAtom <?> "pattern application"

pattern :: Parser (Pat MRel)
pattern = patApp

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

{-
caseExpr :: Parser (TT MRel)
caseExpr = (<?> "case expression") $ do
    n <- freshMN "casefun"
    kwd "case"
    tm <- expr
    kwd "where"
    ty <- expr
    kwd "{"
    alts <- caseAlt `sepBy` kwd ","
    kwd "}"
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
-}

expr :: Parser (TT MRel)
expr = bind <|> app <?> "expression"  -- app includes nullary-applied atoms

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

fundef :: Parser (Def MRel)
fundef = (<?> "definition") $ do
    d <- typing Var
    body <-
        (kwd "." *> clausesBody)
        <|> (kwd "=" *> termBody)
    kwd "."
    return d{ defBody = body }

clausesBody :: Parser (Body MRel)
clausesBody = Clauses <$> (clause `sepBy` kwd ",")

termBody :: Parser (Body MRel)
termBody = Term <$> expr

clause :: Parser (Clause MRel)
clause = (<?> "pattern clause") $ do
    pvs <- (kwd "pat" *> many (parens $ typing Var) <* kwd ".") <|> pure []
    lhs <- pattern
    kwd "="
    rhs <- expr
    return $ Clause pvs lhs rhs

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
