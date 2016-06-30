module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT
import TTLens
import Erasure.Check
import Erasure.Meta
import Erasure.Solve

import Data.Traversable
import qualified Data.Map as M
import qualified Data.Set as S
import Lens.Family2
import Control.Monad
import Control.Applicative
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader

data VerError
    = TCFailure TCFailure
    | InconsistentAnnotation
    | NotImplemented
    deriving Show


data VerFailure = VerFailure VerError [String] deriving Show
type Ver a = ReaderT (VerTraceback, Ctx Relevance) (Except VerFailure) a
type VerTraceback = [String]

runVer :: Ctx Relevance -> Ver a -> Either VerFailure a
runVer ctx ver = runExcept $ runReaderT ver ([], ctx)

verFail :: VerError -> Ver a
verFail e = do
    (tb, ctx) <- ask
    lift . throwE $ VerFailure e tb

verify :: Program Relevance -> Either VerFailure ()
verify prog = runVer (builtins E) $ verProg prog

verProg :: Program Relevance -> Ver ()
verProg (Prog defs) = mapM_ verDef defs

verDef :: Def Relevance -> Ver ()
verDef (Def n r ty b cs) = verFail NotImplemented
