module Args where

import Options.Applicative
import Data.Semigroup ((<>))

data Solver = Simple | Graph | Indexed | LMS deriving (Eq, Ord, Show)

data Args = Args
    { sourceFile :: String
    , verbose :: Bool
    , skipInference :: Bool
    , skipSpecialisation :: Bool
    , skipVerification :: Bool
    , skipEvaluation :: Bool
    , optIdentity :: Bool
    , solver :: Solver
    , dumpPretty :: Maybe String
    , dumpIR :: Maybe String
    , dumpScheme :: Maybe String
    , dumpSchemeIR :: Maybe String
    , dumpNF :: Maybe String
    , dumpNFScheme :: Maybe String
    , rtsSchemePath :: String
    }
    deriving (Show)

args :: Parser Args
args = Args
    <$> strArgument
        ( metavar "source.tt"
        <> help "File with TTstar code")
    <*> switch
        ( long "verbose"
        <> short 'v'
        <> help "Print detailed report of compilation")
    <*> switch
        ( long "skip-inference"
        <> help "Annotate everything as R")
    <*> switch
        ( long "skip-specialisation"
        <> help "Do not specialise erasure-polymorphic functions")
    <*> switch
        ( long "skip-verification"
        <> help "Do not run the verification checker")
    <*> switch
        ( long "skip-evaluation"
        <> help "Do not reduce program to NF")
    <*> switch
        ( long "opt-identity"
        <> help "Enable identity optimisation")
    <*> (option . maybeReader) (`lookup` solvers)
        ( long "solver"
        <> metavar "simple|graph|indexed|lms"
        <> value Indexed
        <> help "Constraint solver to use")
    <*> optional (strOption
        ( metavar "file.tt"
        <> long "dump-pretty"
        <> help "Pretty-print final program"))
    <*> optional (strOption
        ( metavar "file.ir"
        <> long "dump-ir"
        <> help "Pretty-print the IR"))
    <*> optional (strOption
        ( metavar "file.scm"
        <> long "dump-scheme"
        <> help "Generate Scheme source from final program"))
    <*> optional (strOption
        ( metavar "file.scm"
        <> long "dump-scheme-ir"
        <> help "Generate Scheme source from IR"))
    <*> optional (strOption
        ( metavar "fileNF.tt"
        <> long "dump-nf"
        <> help "Pretty-print normal form"))
    <*> optional (strOption
        ( metavar "fileNF.scm"
        <> long "dump-nf-scheme"
        <> help "Generate Scheme source from normal form"))
    <*> strOption
        ( metavar "rts.scm"
        <> long "rts-scm"
        <> value "rts.scm"
        <> help "Embed Scheme RTS from this file")
  where
    solvers = [("simple",Simple),("graph",Graph),("indexed",Indexed),("lms",LMS)]

parse :: IO Args
parse = execParser opts
  where
    opts = info (args <**> helper)
        (fullDesc
        <> header "TTstar -- a dependent language with erasure")

