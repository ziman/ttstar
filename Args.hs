module Args where

import Options.Applicative
import Data.Semigroup ((<>))

data Args = Args
    { sourceFile :: String
    , verbose :: Bool
    , skipInference :: Bool
    , skipVerification :: Bool
    , skipEvaluation :: Bool
    , dumpScheme :: Maybe String
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
        ( long "skip-verification"
        <> help "Do not run the verification checker")
    <*> switch
        ( long "skip-evaluation"
        <> help "Do not reduce program to NF")
    <*> optional (strOption
        ( metavar "file.scm"
        <> long "dump-scm"
        <> help "Generate Scheme source"))

parse :: IO Args
parse = execParser opts
  where
    opts = info (args <**> helper)
        (fullDesc
        <> header "TTstar -- a dependent language with erasure")
