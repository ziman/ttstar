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

with :: Def Relevance -> Ver a -> Ver a
with d = with' $ M.insert (defName d) d

with' :: (Ctx Relevance -> Ctx Relevance) -> Ver a -> Ver a
with' f = local $ \(tb, ctx) -> (tb, f ctx)

bt :: Show a => a -> Ver b -> Ver b
bt dbg sub = do
    ctx <- getCtx
    let btLine = "In context:\n" ++ showCtx ctx ++ "\n" ++ show dbg ++ "\n"
    local (\(tb,ctx) -> (btLine:tb,ctx)) sub

showCtx :: Ctx Relevance -> String
showCtx ctx = unlines
    [ "  " ++ show (defName d) ++ " : " ++ show (defType d)
    | d <- M.elems ctx
    ]

getCtx :: Ver (Ctx Relevance)
getCtx = do
    (tb, ctx) <- ask
    return ctx

verify :: Program Relevance -> Either VerFailure ()
verify prog = runVer (builtins E) $ verProg prog

verProg :: Program Relevance -> Ver ()
verProg (Prog defs) = verDefs defs

verDefs :: [Def Relevance] -> Ver ()
verDefs [] = return ()
verDefs (d:ds) = verDef d *> with d (verDefs ds)

verDef :: Def Relevance -> Ver ()
verDef (Def n r ty b cs) = verFail NotImplemented
