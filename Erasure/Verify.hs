module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT
import TTUtils
import Normalise (whnf)
import Pretty ()

import Control.Monad (when)
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
    | NotConstructor Name
    | ComplexScrutinee (CaseTree Relevance)
    | CantConvert Term Term
    deriving Show

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

mustBeType :: TT Relevance -> Ver ()
mustBeType ty = conv E ty (V typeOfTypes)

verify :: Program Relevance -> Either VerFailure ()
verify prog = runVer (builtins relOfType) $ verProg prog

verProg :: Program Relevance -> Ver ()
verProg prog = do
    _ <- verTm R prog
    return ()

verDefs :: [Def Relevance] -> Ver ()
verDefs [] = return ()
verDefs (d:ds) = with d (verDef d *> verDefs ds)

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
    -- verDefs ds
    let lhs = mkApp (V fn) [(defR d, V $ defName d) | d <- ds]
    verCase r ds lhs ct

verCase :: Relevance -> [Def Relevance] -> Pat -> CaseTree Relevance -> Ver ()
verCase r pvars lhs (Leaf rhs) = bt ("CASE-LEAF", lhs, rhs) $ do
    verDefs pvars
    withs pvars $ do
        lhsTy <- verTm r lhs -- verPat r lhs
        rhsTy <- verTm r rhs
        conv r lhsTy rhsTy

verCase r pvars lhs (Case s (V n) alts) = bt ("CASE-MULTI", n, r, s, lhs) $ do
    d <- lookupPatvar n pvars
    defR d <-> s
    s --> r  -- it's not (<->) because we can have forced inspections, which don't cause usage
    mapM_ (verBranch r pvars lhs n (defType d) r) alts        

verCase r pvars lhs ct@(Case s tm alts) = do
    verFail $ ComplexScrutinee ct

verBranch :: Relevance -> [Def Relevance] -> Pat -> Name -> Type -> Relevance -> Alt Relevance -> Ver ()
verBranch r pvars lhs n scrutTy s (Alt Wildcard rhs) = bt ("ALT-WILD", rhs) $ do
    verCase r pvars lhs rhs

verBranch r pvars lhs n scrutTy s (Alt (Ctor (CT cn u) ds) rhs) = bt ("ALT-MATCH", cn, rhs) $ do
    u --> r
    verBranch' False u pvars lhs n scrutTy s (cn, ds, rhs)

verBranch r pvars lhs n scrutTy s (Alt (Ctor (CTForced cn) ds) rhs) = bt ("ALT-MATCH-F", cn, rhs) $ do
    verBranch' True r pvars lhs n scrutTy s (cn, ds, rhs)

verBranch r pvars lhs n scrutTy s (Alt (ForcedPat pat) rhs) = bt ("ALT-FORCED", pat) $ do
    verCase r (substPV n (Forced pat) pvars) (subst n (Forced pat) lhs) rhs

verBranch' :: Bool -> Relevance -> [Def Relevance] -> Pat -> Name -> Type -> Relevance
    -> (Name, [Def Relevance], CaseTree Relevance)
    -> Ver ()
verBranch' ctorForced r pvars lhs n scrutTy s (cn, ds, rhs) = bt ("ALT-MATCH-INT", cn, rhs) $ do
    cd <- lookupName cn
    when (defBody cd /= Abstract Postulate) $
        verFail (NotConstructor cn)

    --withs pvars $ verDefs ds  -- do we check the args here or only in the leaf?

    sequence_ [defR d --> s | d <- ds]
    bt("ALT-MATCH-INT2", r, s, pat, scrutTy) $ do
        {- this is just not true
        -- check that the pattern matches the scrutinee
        --
        -- TODO/FIXME:
        -- Why the pattern has to be checked using verTm
        -- rather than verPat is a mystery to me. What's going on?
        --
        let scrutTy' = subst n pat scrutTy
        patTy <- verTm (r /\ s) pat --  verPat (op r s) pat''  -- TODO: figure this out
        conv (r /\ s) patTy scrutTy'
        -}
        verCase r (substPV n pat pvars ++ ds) (subst n pat lhs) rhs
  where
    pat = mkApp c' [(defR d, V $ defName d) | d <- ds]
    c' = if ctorForced
            then Forced (V cn)
            else V cn

substPV :: Name -> TT Relevance -> [Def Relevance] -> [Def Relevance]
substPV n tm [] = []
substPV n tm (d:ds)
    | defName d == n = substPV n tm ds
    | otherwise = subst n tm d : substPV n tm ds

lookupPatvar :: Name -> [Def Relevance] -> Ver (Def Relevance)
lookupPatvar n [] = verFail $ NotPatvar n
lookupPatvar n (d:ds)
    | defName d == n
    = return d

    | otherwise
    = lookupPatvar n ds

verTm :: Relevance -> Term -> Ver Type
verTm E (V n) = bt ("VAR-E", n) $ do
    d <- lookupName n
    return $ defType d

verTm R (V n) = bt ("VAR-R", n) $ do
    d <- lookupName n
    defR d <-> R
    return $ defType d

verTm r (Bind Lam [d@(Def n s ty (Abstract Var) _)] tm) = bt ("LAM", r, n) $ do
    tyty <- verTm E ty    
    mustBeType tyty
    tmty <- with d $ verTm r tm
    return $ Bind Pi [d] tmty

verTm r (Bind Pi [d@(Def n s ty (Abstract Var) _)] tm) = bt ("PI", r, n) $ do
    tyty <- verTm E ty
    mustBeType tyty
    tmty <- with d $ verTm r tm
    mustBeType tmty
    return (V typeOfTypes)

verTm r (Bind Let ds tm) = bt ("LET", r, ds) $ do
    verDefs ds
    withs ds $ verTm r tm

verTm r (App s f x) = bt ("APP", r, f, s, x) $ do
    ctx <- getCtx
    fty <- verTm r f
    case whnf ctx fty of
        Bind Pi [Def n s piTy (Abstract Var) _] piRhs -> do
            xty <- verTm (r /\ s) x
            conv (r /\ s) xty piTy            
            return $ subst n x piRhs

        _ -> verFail $ NotPi fty

verTm r (Forced tm) = bt ("FORCED", tm) $ do
    verTm r tm

verTm r tm = bt ("UNKNOWN-TERM", tm) $ do
    verFail NotImplemented

{-
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
        Bind Pi [Def n s piTy (Abstract Var) _] piRhs -> do
            xty <- verTm r x
            conv r xty piTy  -- here, conversion check may be R
            r <-> s          -- but r and s must match
            return $ subst n x piRhs

        _ -> verFail $ NotPi fty

verPat E (App r f x) = bt ("PAT-APP-E", f, x) $ do
    ctx <- getCtx
    fty <- verTm E f
    case whnf ctx fty of
        Bind Pi [Def n s piTy (Abstract Var) _] piRhs -> do
            xty <- verTm E x
            conv E xty piTy   -- here, conversion check must be E, but r and s needn't match
            return $ subst n x piRhs

        _ -> verFail $ NotPi fty

verPat r (Forced tm) = bt ("PAT-FORCED", tm) $ do
    verTm E tm

verPat r pat = verFail NotImplemented
-}

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
    (Bind b  [d@(Def  n  r  ty  (Abstract Var) _)] tm)
    (Bind b' [d'@(Def n' r' ty' (Abstract Var) _)] tm')
    | b == b' = bt ("CONV-BIND", b, d, tm, d', tm') $ do
        r <-> r'
        conv R ty ty'
        with d $ 
            conv R tm (subst n' (V n) tm')

conv' E
    (Bind b  [d@(Def  n  r  ty  (Abstract Var) _)] tm)
    (Bind b' [d'@(Def n' r' ty' (Abstract Var) _)] tm')
    | b == b' = bt ("CONV-BIND", b, d, tm, d', tm') $ do
        conv E ty ty'
        with d $ 
            conv E tm (subst n' (V n) tm')

{- This would be necessary for conversion-checking of multilets. Let's disable them for now.
conv' r (Bind b (d:ds) tm) (Bind b' (d':ds') tm')
    = bt ("CONV-SIMPL", b) $
        conv' r (Bind b [d] $ Bind b ds tm) (Bind b' [d'] $ Bind b' ds' tm')
-}

conv' r p q = verFail $ CantConvert p q
