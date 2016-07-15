module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT
import TTUtils
import Normalise (whnf)
import Pretty ()

import qualified Data.Map as M
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader

data VerError
    = UnknownName Name
    | RelevanceMismatch Relevance Relevance
    | NotPi Term
    | NotPatvar Name
    | NotImplemented
    | ComplexScrutinee (CaseTree Relevance)
    | CantConvert Term Term
    deriving Show

data Cardinality = Single | Many deriving (Eq, Ord, Show)

data VerFailure = VerFailure VerError [String]
type Ver a = ReaderT (VerTraceback, Ctx Relevance) (Except VerFailure) a
type VerTraceback = [String]

type Term = TT Relevance
type Type = TT Relevance
type Pat  = TT Relevance

instance Show VerFailure where
    show (VerFailure e []) = show e
    show (VerFailure e tb) = unlines $
            "Traceback:"
            : zipWith
                (\i n -> show i ++ ". " ++ n)
                [1::Integer ..]
                (reverse tb)
            ++ ["Error: " ++ show e]

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

infix 3 <->
(<->) :: Relevance -> Relevance -> Ver ()
(<->) = eqR

infix 3 -->
(-->) :: Relevance -> Relevance -> Ver ()
R --> E = verFail $ RelevanceMismatch R E
_ --> _ = return ()


infixr 3 /\
(/\) :: Relevance -> Relevance -> Relevance
R /\ R = R
_ /\ _ = E

hasRelevance :: Name -> Relevance -> Ver ()
hasRelevance n r = do
    d <- lookupName n
    if (r == R) && (defR d == E)
        then verFail $ RelevanceMismatch r (defR d)
        else return ()

mustBeType :: TT Relevance -> Ver ()
mustBeType ty = conv E ty (V typeOfTypes)

verify :: Program Relevance -> Either VerFailure ()
verify prog = runVer (builtins relOfType) $ verProg prog

verProg :: Program Relevance -> Ver ()
verProg (Prog defs) = verDefs defs

verDefs :: [Def Relevance] -> Ver ()
verDefs [] = return ()
verDefs (d:ds) = verDef d *> with d (verDefs ds)

verDef :: Def Relevance -> Ver ()
verDef (Def n r ty (Abstract _) cs) = bt ("DEF-ABSTR", n) $ do
    tyty <- verTm E ty
    mustBeType tyty

verDef d@(Def n r ty (Term tm) cs) = bt ("DEF-TERM", n) $ do
    tyty <- verTm E ty
    mustBeType tyty
    tmty <- with d $ verTm r tm
    conv r tmty ty

verDef d@(Def n r ty (Patterns cf) cs) = bt ("DEF-TERM", n) $ do
    tyty <- verTm E ty
    mustBeType tyty
    with d $
        verCaseFun n r cf

verCaseFun :: Name -> Relevance -> CaseFun Relevance -> Ver ()
verCaseFun fn r (CaseFun ds ct) = bt ("CASEFUN", fn) $ do
    verDefs ds
    let lhs = mkApp (V fn) [(defR d, V $ defName d) | d <- ds]
    withs ds $
        verCase r lhs ct

verCase :: Relevance -> Pat -> CaseTree Relevance -> Ver ()
verCase r lhs (Leaf rhs) = bt ("CASE-LEAF", lhs, rhs) $ do
    lhsTy <- verPat r lhs
    rhsTy <- verTm  r rhs
    conv r lhsTy rhsTy

verCase R lhs (Case s (V n) [alt]) = bt ("CASE-SING-R", lhs) $ do
    d <- lookupName n    
    defR d <-> s
    verBranch Single R lhs n s alt

verCase E lhs (Case E (V n) [alt]) = bt ("CASE-SING-E", lhs) $ do
    _ <- lookupName n  -- make sure the name exists
    verBranch Single E lhs n E alt

verCase r lhs (Case s (V n) alts) = bt ("CASE-MULTI", r, lhs) $ do
    r <-> s
    n `hasRelevance` r
    mapM_ (verBranch Many r lhs n r) alts        

verCase r lhs ct@(Case s tm alts) = do
    verFail $ ComplexScrutinee ct

verBranch :: Cardinality -> Relevance -> Pat -> Name -> Relevance -> Alt Relevance -> Ver ()
verBranch q r lhs n s (Alt Wildcard rhs) = bt ("ALT-WILD", rhs) $ do
    verCase r lhs rhs

verBranch q r lhs n s (Alt (Ctor u cn ds eqs) rhs) = bt ("ALT-MATCH", cn, rhs) $ do
    u --> r
    verBranch' q u lhs n s (cn, ds, eqs, rhs)

verBranch' :: Cardinality -> Relevance -> Pat -> Name -> Relevance
    -> (Name, [Def Relevance], [(Name, TT Relevance)], CaseTree Relevance)
    -> Ver ()
verBranch' q r lhs n s (cn, ds, eqs, rhs) = bt ("ALT-MATCH-INT", cn, rhs) $ do
    verDefs ds
    let pat = mkApp c' [(defR d, V $ defName d) | d <- ds]
    let eqs' = [(n, Forced tm) | (n, tm) <- eqs]
    let eqs'' = (n, substs eqs' pat) : eqs'
    let lhs'' = substs eqs'' lhs
    let rhs'' = substs eqs'' rhs
    mapM_ (--> s) [defR d | d <- ds]
    withs ds $ do
        localVars eqs
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
verTm E (V n) = bt ("VAR-E", n) $ do
    d <- lookupName n
    return $ defType d

verTm R (V n) = bt ("VAR-R", n) $ do
    d <- lookupName n
    defR d <-> R
    return $ defType d

verTm r (Bind Lam d@(Def n s ty (Abstract Var) _) tm) = bt ("LAM", r, n) $ do
    tyty <- verTm E ty    
    mustBeType tyty
    tmty <- with d $ verTm r tm
    return $ Bind Pi d tmty

verTm r (Bind Pi d@(Def n s ty (Abstract Var) _) tm) = bt ("PI", r, n) $ do
    tyty <- verTm E ty
    mustBeType tyty
    tmty <- with d $ verTm r tm
    mustBeType tmty
    return (V typeOfTypes)

verTm r (Bind Let d tm) = bt ("LET", r, d) $ do
    verDef d
    with d $ verTm r tm

verTm r (App s f x) = bt ("APP", r, f, s, x) $ do
    ctx <- getCtx
    fty <- verTm r f
    case whnf ctx fty of
        Bind Pi (Def n s piTy (Abstract Var) _) piRhs -> do
            xty <- verTm (r /\ s) x
            conv (r /\ s) xty piTy            
            return $ subst n x piRhs

        _ -> verFail $ NotPi fty

verTm r (Forced tm) = bt ("FORCED", tm) $ do
    verTm r tm

verTm r tm = bt ("UNKNOWN-TERM", tm) $ do
    verFail NotImplemented

verPat :: Relevance -> Pat -> Ver Type
verPat R (V n) = bt ("PAT-REF-R", n) $ do
    defType <$> lookupName n    

verPat E (V n) = bt ("PAT-REF-E", n) $ do
    d <- lookupName n
    defR d <-> E
    return $ defType d

verPat R (App r f x) = bt ("PAT-APP-R", f, x) $ do
    ctx <- getCtx
    fty <- verTm R f
    case whnf ctx fty of
        Bind Pi (Def n s piTy (Abstract Var) _) piRhs -> do
            xty <- verTm r x
            conv r xty piTy  -- here, conversion check may be R
            r <-> s          -- but r and s must match
            return $ subst n x piRhs

        _ -> verFail $ NotPi fty

verPat E (App r f x) = bt ("PAT-APP-E", f, x) $ do
    ctx <- getCtx
    fty <- verTm E f
    case whnf ctx fty of
        Bind Pi (Def n s piTy (Abstract Var) _) piRhs -> do
            xty <- verTm E x
            conv E xty piTy   -- here, conversion check must be E, but r and s needn't match
            return $ subst n x piRhs

        _ -> verFail $ NotPi fty

verPat r (Forced tm) = bt ("PAT-FORCED", tm) $ do
    verTm E tm

verPat r pat = verFail NotImplemented

conv :: Relevance -> Type -> Type -> Ver ()
conv r p q = do
    ctx <- getCtx
    conv' r (whnf ctx p) (whnf ctx q)
    
conv' :: Relevance -> Type -> Type -> Ver ()
conv' r (V n) (V n')
    | n == n' = return ()

conv' R (App r f x) (App r' f' x') = bt ("CONV-APP-R", f, x, f', x') $ do
    r <-> r'
    conv R f f'
    conv R x x'

conv' E (App r f x) (App r' f' x') = bt ("CONV-APP-E", f, x, f', x') $ do
    conv E f f'
    conv E x x'

conv' R
    (Bind b  d@(Def  n  r  ty  (Abstract Var) _) tm)
    (Bind b' d'@(Def n' r' ty' (Abstract Var) _) tm')
    | b == b' = bt ("CONV-BIND", b, d, tm, d', tm') $ do
        r <-> r'
        conv R ty ty'
        with d $ 
            conv R tm (subst n' (V n) tm')

conv' E
    (Bind b  d@(Def  n  r  ty  (Abstract Var) _) tm)
    (Bind b' d'@(Def n' r' ty' (Abstract Var) _) tm')
    | b == b' = bt ("CONV-BIND", b, d, tm, d', tm') $ do
        conv E ty ty'
        with d $ 
            conv E tm (subst n' (V n) tm')

conv' r p q = verFail $ CantConvert p q
