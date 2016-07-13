module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT
import TTUtils
import Pretty ()

import qualified Data.Map as M
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader

data VerError
    = UnknownName Name
    | RelevanceMismatch Relevance Relevance
    | NotPatvar Name
    | NotImplemented
    | ComplexScrutinee (CaseTree Relevance)
    deriving Show

data Cardinality = Single | Many deriving (Eq, Ord, Show)

data VerFailure = VerFailure VerError [String] deriving Show
type Ver a = ReaderT (VerTraceback, Ctx Relevance) (Except VerFailure) a
type VerTraceback = [String]

type Term = TT Relevance
type Type = TT Relevance
type Pat  = TT Relevance

runVer :: Ctx Relevance -> Ver a -> Either VerFailure a
runVer ctx ver = runExcept $ runReaderT ver ([], ctx)

verFail :: VerError -> Ver a
verFail e = do
    (tb, ctx) <- ask
    lift . throwE $ VerFailure e tb

with :: Def Relevance -> Ver a -> Ver a
with d = with' $ M.insert (defName d) d

withs :: [Def Relevance] -> Ver a -> Ver a
withs [] = id
withs (d:ds) = with d . withs ds

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

lookupName :: Name -> Ver (Def Relevance)
lookupName n = do
    ctx <- getCtx
    case M.lookup n ctx of
        Just x  -> return x
        Nothing -> verFail $ UnknownName n

eqR :: Relevance -> Relevance -> Ver ()
eqR r s
    | r == s = return ()
    | otherwise = verFail $ RelevanceMismatch r s

hasRelevance :: Name -> Relevance -> Ver ()
hasRelevance n r = do
    d <- lookupName n
    if (r == R) && (defR d == E)
        then verFail $ RelevanceMismatch r (defR d)
        else return ()

verify :: Program Relevance -> Either VerFailure ()
verify prog = runVer (builtins E) $ verProg prog

verProg :: Program Relevance -> Ver ()
verProg (Prog defs) = verDefs defs

verDefs :: [Def Relevance] -> Ver ()
verDefs [] = return ()
verDefs (d:ds) = verDef d *> with d (verDefs ds)

verDef :: Def Relevance -> Ver ()
verDef (Def n r ty (Abstract _) cs) = do
    tyty <- verTm E ty
    conv E tyty (V $ UN "Type")

verDef d@(Def n r ty (Term tm) cs) = do
    tyty <- verTm E ty
    conv E tyty (V $ UN "Type")
    tmty <- with d $ verTm r tm
    conv r tmty ty

verDef d@(Def n r ty (Patterns cf) cs) = do
    tyty <- verTm E ty
    conv E tyty (V $ UN "Type")
    with d $
        verCaseFun n r cf

verCaseFun :: Name -> Relevance -> CaseFun Relevance -> Ver ()
verCaseFun fn r (CaseFun ds ct) = do
    verDefs ds
    let lhs = mkApp (V fn) [(defR d, V $ defName d) | d <- ds]
    withs ds $
        verCase r lhs ct

verCase :: Relevance -> Pat -> CaseTree Relevance -> Ver ()
verCase r lhs (Leaf rhs) = do
    lhsTy <- verPat r lhs
    rhsTy <- verTm  r rhs
    conv r lhsTy rhsTy

verCase R lhs (Case s (V n) [alt]) = do
    d <- lookupName n    
    eqR s (defR d)
    verBranch Single R lhs n s alt

verCase E lhs (Case E (V n) [alt]) = do
    _ <- lookupName n  -- make sure the name exists
    verBranch Single E lhs n E alt

verCase r lhs (Case s (V n) alts) = do
    eqR r s
    n `hasRelevance` r
    mapM_ (verBranch Many r lhs n r) alts        

verCase r lhs ct@(Case s tm alts) = do
    verFail $ ComplexScrutinee ct

verBranch :: Cardinality -> Relevance -> Pat -> Name -> Relevance -> Alt Relevance -> Ver ()
verBranch q r lhs n s (Alt Wildcard rhs) = do
    verCase r lhs rhs
verBranch q r lhs n s (Alt (Ctor cn ds eqs) rhs) = do
    verDefs ds
    localVars eqs
    let pat = mkApp c' [(defR d, V $ defName d) | d <- ds]
    let eqs' = [(n, Forced tm) | (n, tm) <- eqs]
    let eqs'' = (n, substs eqs' pat) : eqs'
    let lhs'' = substs eqs'' lhs
    let rhs'' = substs eqs'' rhs
    withs ds $
        with' (substsInCtx eqs'') $
            verCase r lhs'' rhs''
  where
    c' :: Pat
    c' = case q of
            Single -> Forced (V cn)
            Many   -> V cn

    localVars :: [(Name, Term)] -> Ver ()
    localVars [] = return ()
    localVars ((n,tm):eqs) = do
        d <- lookupName n
        case defBody d of
            Abstract Var -> localVars eqs
            _ -> verFail $ NotPatvar n


verTm :: Relevance -> Term -> Ver Type
verTm r tm = bt ("TERM", tm) $ verFail NotImplemented

verPat :: Relevance -> Pat -> Ver Type
verPat r pat = verFail NotImplemented

conv :: Relevance -> Type -> Type -> Ver ()
conv r p q = verFail NotImplemented
