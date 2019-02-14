module TT.Parser (readProgram) where

import TT.Core
import TT.Utils
import TT.Pretty ()

import Data.Char
import Text.Parsec
import System.FilePath
import qualified Data.Map as M
import qualified Data.Set as S

data ParserState = PS
    { psCounters :: M.Map String Int
    }
    deriving (Eq, Ord, Show)

type Parser = Parsec String ParserState
type MRel = Maybe Relevance

readProgram :: String -> IO (Either ParseError (Program MRel))
readProgram fname = do
    ds' <- readDefs fname
    case ds' of
        Left err -> return . Left  $ err
        Right ds -> return . Right $ Bind Let ds (V $ UN "main")

readDefs :: String -> IO (Either ParseError [Def MRel])
readDefs fname = do
    body <- readFile fname
    case runParser program initialParserState fname body of
        Left err -> return $ Left err
        Right (is, ds) -> do
            let rootDir = takeDirectory fname
            dss' <- sequence <$> mapM readDefs [rootDir </> i | i <- is]
            case dss' of
                Left  err -> return . Left  $ err
                Right dss -> return . Right $ concat dss ++ ds

initialParserState :: ParserState
initialParserState = PS
    { psCounters = M.empty
    }

freshMN :: String -> Parser Name
freshMN stem = do
    st <- getState
    let cs = psCounters st
    let i = M.findWithDefault 1 stem cs
    putState st{ psCounters = M.insert stem (i+1) cs }
    return $ MN stem i

keywords :: S.Set String
keywords = S.fromList [
    "case", "with", "where",
    "data", "let", "in", "postulate",
    "of", "forall"
  ]

lineComment :: Parser ()
lineComment = kwd "--" *> many (satisfy (/= '\n')) *> return () <?> "line comment"

bigComment :: Parser ()
bigComment = kwd "{-" *> manyTill anyChar (try $ kwd "-}") *> return () <?> "block comment"

sp :: Parser ()
sp = many ((satisfy isSpace *> return ()) <|> lineComment <|> bigComment) *> return () <?> "whitespace or comment"

kwd :: String -> Parser ()
kwd s = (try (string s) >> sp) <?> s

identifier :: Parser Name
identifier = (<?> "identifier") $ do
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

blankName :: Parser Name
blankName = kwd "_" *> freshMN "" <?> "blank name"

name :: Parser Name
name = identifier <|> blankName <?> "name"

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

meta :: Parser (TT MRel)
meta = kwd "_" *> freshMeta

freshMeta :: Parser (TT MRel)
freshMeta = do
    ~(MN _ i) <- freshMN "_"
    return $ Meta i

atomic :: Parser (TT MRel)
atomic = parens expr
    <|> caseExpr
    <|> erasureInstance
    <|> meta
    <|> var
    <|> natural
    <?> "atomic expression"

arrow :: Parser (TT MRel)
arrow = (<?> "arrow type") $ do
    n <- freshMN "x"
    ty <- try (app <* kwd "->")  -- app includes nullary applications (atoms)
    Bind Pi [Def n Nothing ty (Abstract Var)] <$> expr

lambda :: Parser (TT MRel)
lambda = (<?> "lambda") $ do
    kwd "\\"
    d' <- (Right <$> ptyping Var)
        <|> try (Right <$> typing Var)
        <|> (Left <$> name)
    kwd "."

    case d' of
        Right d -> Bind Lam [d] <$> expr
        Left n -> do
            ty <- freshMeta
            Bind Lam [Def n Nothing ty (Abstract Var)] <$> expr

bpi :: Parser (TT MRel)
bpi = (<?> "pi") $ do
    d <- try $ ptyping Var
    kwd "->"
    Bind Pi [d] <$> expr

-- meta-enabled typings
mtypings :: Parser [Def MRel]
mtypings = traverse f =<< many1 ((Left <$> name) <|> (Right <$> typing Var))
  where
    f (Left n) = do
        ty <- freshMeta
        return $ Def n Nothing ty (Abstract Var)

    f (Right d) = return d

bforall :: Parser (TT MRel)
bforall = (<?> "forall") $ do
    kwd "forall"
    ds <- mtypings
    kwd "->"
    rhs <- expr
    pure $ foldr (\d rhs' -> Bind Pi [d] rhs') rhs ds

bind :: Parser (TT MRel)
bind = arrow
    <|> lambda
    <|> bpi
    <|> bforall
    <|> let_
    <?> "binder"

stringLiteral :: Parser String
stringLiteral = (<?> "string literal") $ do
    kwd "\""
    s <- many stringChar
    kwd "\""
    return s
  where
    stringChar :: Parser Char
    stringChar =
        satisfy (/= '"')
        <|> (kwd "\\\"" *> return '"')
        <|> (kwd "\\\\" *> return '\\')

app :: Parser (TT MRel)
app = (<?> "application") $ do
    f <- atomic
    args <- many appArg
    return $ mkApp f args

appArg :: Parser (MRel, TT MRel)
appArg =
    ((,) <$> pure (Just I) <*> try (string "." *> atomic))
    <|> ((,) <$> pure Nothing <*> atomic)
    <?> "application argument"

brackets :: Parser a -> Parser a
brackets p = kwd "[" *> p <* kwd "]"

braces :: Parser a -> Parser a
braces p = kwd "{" *> p <* kwd "}"

patVar :: Parser (Pat MRel)
patVar = PV <$> name <?> "pattern variable"

patForced :: Parser (Pat MRel)
patForced = PForced <$> brackets expr <?> "forced pattern"

forcedCtor :: Parser (Pat MRel)
forcedCtor = PForced . V <$> braces name <?> "forced constructor"

patAtom :: Parser (Pat MRel)
patAtom = parens pattern <|> forcedCtor <|> patForced <|> patVar <?> "pattern atom"

patAppArg :: Parser (MRel, Pat MRel)
patAppArg =
    ((,) <$> pure (Just I) <*> try (string "." *> patAtom))
    <|> ((,) <$> pure Nothing <*> patAtom)
    <?> "pattern application argument"

patApp :: Parser (Pat MRel)
patApp = (<?> "pattern application") $ do
    f <- patAtom
    args <- many patAppArg
    return $ mkAppPat f args

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
    return $ EI n ty

caseExpr :: Parser (TT MRel)
caseExpr = (<?> "case expression") $ do
    kwd "case"
    tms <- expr `sepBy` kwd ","
    kwd "with"
    d <- clauseDef
    return $ Bind Let [d] (mkApp (V $ defName d) $ zip (repeat Nothing) tms)

expr :: Parser (TT MRel)
expr = bind <|> app <?> "expression"  -- app includes nullary-applied atoms

typing :: Abstractness -> Parser (Def MRel)
typing a = (<?> "name binding") $ do
    n <- name
    r <- rcolon
    ty <- expr
    return $ Def n r ty (Abstract a)

ptyping :: Abstractness -> Parser (Def MRel)
ptyping abs =
    (parens (typing abs))
    <|> try (string "." *> parens (makeIrrelevant <$> typing abs))
  where
    makeIrrelevant def = def{ defR = Just I }

postulate :: Parser (Def MRel)
postulate = (<?> "postulate") $ do
    kwd "postulate"
    d <- typing Postulate
    return d

clauseDef :: Parser (Def MRel)
clauseDef = (<?> "pattern-clause definition") $ do
    d <- typing Var
    body <-
        (kwd "." *> clausesBody)
        <|> (kwd "=" *> termBody)
    return d{ defBody = body }

mlDef :: Parser (Def MRel)
mlDef = (<?> "ml-style definition") $ do
    n <- try (name <* kwd "\\")
    args <- many (ptyping Var)
    r <- rcolon
    retTy <- expr
    kwd "="
    rhs <- expr
    return $ Def n r (mkPi args retTy) (Term $ mkLam args rhs)
  where
    mkLam [] rhs = rhs
    mkLam (d:ds) rhs = Bind Lam [d] $ mkLam ds rhs

    mkPi [] retTy = retTy
    mkPi (d:ds) retTy = Bind Pi [d] $ mkPi ds retTy

clausesBody :: Parser (Body MRel)
clausesBody = Clauses <$> (clause `sepBy` kwd ",") <* optional (kwd ".")

termBody :: Parser (Body MRel)
termBody = Term <$> expr

mpatvars :: Parser [Def MRel]
mpatvars = kwd "pat" *> mtypings <* kwd "."

clause :: Parser (Clause MRel)
clause = (<?> "pattern clause") $ do
    pvs <- mpatvars <|> many (ptyping Var)
    lhs <- forceHead <$> pattern
    kwd "="
    rhs <- expr
    return $ Clause pvs lhs rhs

forceHead :: Pat MRel -> Pat MRel
forceHead p | (PV f, args) <- unApplyPat p
    = mkAppPat (PHead f) args
forceHead p
    = error $ "invalid clause LHS: " ++ show p

dataDef :: Parser [Def MRel]
dataDef = (<?> "data definition") $ do
    kwd "data"
    tfd <- typing Constructor
    kwd "where"
    ctors <- typing Constructor `sepBy` kwd ","
    return (tfd : ctors)

foreignDef :: Parser (Def MRel)
foreignDef = (<?> "foreign definition") $ do
    kwd "foreign"
    d <- typing $ Foreign undefined
    kwd "="
    code <- stringLiteral
    return d{defBody = Abstract $ Foreign code}

simpleDef :: Parser (Def MRel)
simpleDef = foreignDef <|> postulate <|> mlDef <|> clauseDef <?> "simple definition"

imports :: Parser [String]
imports = many (kwd "import" *> stringLiteral)

definition :: Parser [Def MRel]
definition = dataDef <|> (pure <$> simpleDef) <?> "definition"

definitions :: Parser [Def MRel]
definitions = concat <$> many (definition <* optional (kwd ".")) <?> "definitions"

program :: Parser ([String], [Def MRel])
program = (<?> "program") $ do
    sp
    is <- imports
    ds <- definitions
    eof
    return (is, ds)

-- vim: set et
