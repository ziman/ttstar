module TT.Parser (readProgram) where

import TT.Core
import TT.Utils
import TT.Lens
import TT.Pretty ()

import Data.Char
import Data.Functor
import Text.Parsec
import System.FilePath
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Text.Parsec.Indent as PI
import qualified Control.Monad.Trans.State.Strict as ST

data ParserState = PS
    { psCounters :: M.Map String Int
    }
    deriving (Eq, Ord, Show)

type Parser a = PI.IndentParser String ParserState a
type MRel = Maybe Relevance

-- 2D layout --
-- the ticked versions allow being right on the fence
-- the unticked versions require at least one indent

withinFence :: Parser ()
withinFence = PI.sameOrIndented

withinFence' :: Parser ()
withinFence' = PI.sameOrIndented <|> PI.checkIndent

subfenced :: Parser a -> Parser a
subfenced x = withinFence >> PI.withPos x

subfenced' :: Parser a -> Parser a
subfenced' x = withinFence' >> PI.withPos x

-- Rest of parser --

readProgram :: String -> IO (Either ParseError (Program MRel))
readProgram fname =
    readDefs fname <&> \case
        Left err -> Left  $ err
        Right ds ->
            let prog = Bind Let ds (V $ UN "main")
                f _ = ST.get >>= \i -> ST.put (i+1) >> pure (Meta i)
              in Right $ ST.evalState (ttMetas f prog) 0

readDefs :: String -> IO (Either ParseError [Def MRel])
readDefs fname = do
    body <- readFile fname
    case PI.runIndentParser program initialParserState fname body of
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
    let i = M.findWithDefault 0 stem cs
    putState st{ psCounters = M.insert stem (i+1) cs }
    return $ MN stem i

keywords :: S.Set String
keywords = S.fromList [
    "case", "with", "where",
    "data", "let", "in", "postulate",
    "of", "forall", "do"
  ]

-- this is not a kwd because we don't care about alignment
lineComment :: Parser ()
lineComment = try (string "--") *> many (satisfy (/= '\n')) *> return () <?> "line comment"

-- this is not a kwd because we don't care about alignment
bigComment :: Parser ()
bigComment = try (string "{-") *> manyTill anyChar (try $ string "-}") *> return () <?> "block comment"

sp :: Parser ()
sp = many
    ( (satisfy isSpace *> return ())
    <|> lineComment
    <|> bigComment
    )
    *> return ()
    <?> "whitespace or comment"

kwd :: String -> Parser ()
kwd s = (withinFence >> try (string s) >> sp) <?> s

identifier :: Parser Name
identifier = (<?> "identifier") $ do
    withinFence
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
natural = mkNat . read <$> (withinFence *> many1 (satisfy isDigit) <* sp) <?> "number"
  where
    mkNat :: Int -> TT MRel
    mkNat 0 = V $ UN "Z"
    mkNat k = App Nothing (V $ UN "S") (mkNat (k-1))

metaVar :: Parser (TT MRel)
metaVar = kwd "_" *> pure meta

meta :: TT MRel
meta = Meta (error "meta numbers not defined in parser")

atomic :: Parser (TT MRel)
atomic = parens expr
    <|> caseExpr
    <|> erasureInstance
    <|> metaVar
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
        Left n -> Bind Lam [Def n Nothing meta (Abstract Var)] <$> expr

bpi :: Parser (TT MRel)
bpi = (<?> "pi") $ do
    d <- try $ ptyping Var
    kwd "->"
    Bind Pi [d] <$> expr

-- meta-enabled typings
mtypings :: Parser [Def MRel]
mtypings = many1 (nm <|> ptyping Var)
  where
    nm  = name <&> \n -> Def n Nothing meta (Abstract Var)

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
    withinFence
    _ <- string "\""
    s <- many stringChar
    _ <- string "\""
    sp
    return s
  where
    stringChar :: Parser Char
    stringChar =
        satisfy (/= '"')
        <|> (kwd "\\\"" *> return '"')
        <|> (kwd "\\\\" *> return '\\')

app :: Parser (TT MRel)
app = (<?> "application") $ subfenced $ do
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
patApp = (<?> "pattern application") $ subfenced $ do
    f <- patAtom
    args <- many patAppArg
    return $ mkAppPat f args

pattern :: Parser (Pat MRel)
pattern = patApp

let_ :: Parser (TT MRel)
let_ = (<?> "let expression") $ subfenced $ do
    ds <- subfenced' $ kwd "let" *> many1 simpleDef
    subfenced' $ kwd "in" *> (Bind Let ds <$> expr)

erasureInstance :: Parser (TT MRel)
erasureInstance = (<?> "erasure instance") $ do
    kwd "["
    n <- name
    kwd ":"
    ty <- expr
    kwd "]"
    return $ EI n ty

caseExpr :: Parser (TT MRel)
caseExpr = (<?> "case expression") $ subfenced $ do
    kwd "case"
    tms <- expr `sepBy` kwd ","
    d   <- caseOf (length tms) <|> caseWith
    return $ Bind Let [d] (mkApp (V $ defName d) $ zip (repeat Nothing) tms)

caseWith :: Parser (Def MRel)
caseWith = kwd "with" >> clauseDef

caseOf :: Int -> Parser (Def MRel)
caseOf nscruts = do
    kwd "of"
    fn  <- freshMN "cf"
    fty <- mkPi nscruts
    Def fn Nothing fty . Clauses <$> many (caseArm fn)
  where
    mkPi :: Int -> Parser (TT MRel)
    mkPi 0 = pure meta
    mkPi k = do
        n <- freshMN "cft"
        Bind Pi [Def n Nothing meta $ Abstract Var] <$> mkPi (k-1)

    caseArm :: Name -> Parser (Clause MRel)
    caseArm fn = subfenced $ do
        parserTrace "caseArm"
        pvs <- mpatvars <|> pure []
        parserTrace "caseArm2"
        lhs <- pattern `sepBy1` kwd ","
        parserTrace "caseArm3"
        kwd "="
        Clause pvs (mkAppPat (PHead fn) [(Nothing, p) | p <- lhs]) <$> expr

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
postulate = (<?> "postulate") $ subfenced $ do
    kwd "postulate"
    d <- typing Postulate
    return d

clauseDef :: Parser (Def MRel)
clauseDef = (<?> "pattern-clause definition") $ do
    d <- subfenced' $ typing Var
    body <-
        (kwd "=" *> termBody)
        <|> clausesBody
    return d{ defBody = body }

mlDef :: Parser (Def MRel)
mlDef = (<?> "ml-style definition") $ subfenced' $ do
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
clausesBody = Clauses <$> many clause

termBody :: Parser (Body MRel)
termBody = Term <$> expr

mpatvars :: Parser [Def MRel]
mpatvars = subfenced' (kwd "forall" *> mtypings <* optional (kwd "."))

clause :: Parser (Clause MRel)
clause = (<?> "pattern clause") $ subfenced' $ do
    -- quickly reject common beginnings of the next decl
    notFollowedBy (name >> kwd ":")
    notFollowedBy (name >> kwd "\\")
    pvs <- mpatvars <|> many (ptyping Var)
    subfenced' $ do
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
dataDef = (<?> "data definition") $ subfenced' $ do
    tfd <- kwd "data" *> typing Constructor <* kwd "where"
    ctors <- many (subfenced $ typing Constructor)
    return (tfd : ctors)

foreignDef :: Parser (Def MRel)
foreignDef = (<?> "foreign definition") $ subfenced' $ do
    kwd "foreign"
    d <- typing $ Foreign undefined
    kwd "="
    code <- stringLiteral
    return d{defBody = Abstract $ Foreign code}

simpleDef :: Parser (Def MRel)
simpleDef = foreignDef <|> postulate <|> mlDef <|> clauseDef <?> "simple definition"

imports :: Parser [String]
imports = many (subfenced' $ kwd "import" *> stringLiteral)

definition :: Parser [Def MRel]
definition = dataDef <|> (pure <$> simpleDef) <?> "definition"

definitions :: Parser [Def MRel]
definitions = concat <$> many definition <?> "definitions"

program :: Parser ([String], [Def MRel])
program = (<?> "program") $ do
    sp
    is <- imports
    ds <- definitions
    eof
    return (is, ds)

-- vim: set et
