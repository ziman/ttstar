module Erasure.Verify
    ( verify
    , VerError(..)
    ) where

import TT.Core
import TT.Utils
import TT.Normalise (whnf)
import TT.Pretty (prettyCol)

import qualified Data.Set as S
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
    | NotConstructorHead Term
    | BadPatAppHead (Pat Relevance)
    | NotClauses Name
    | CantConvert Term Term
    | PatvarsPatternMismatch [Name] [Name]
    | NonLinearPattern (Pat Relevance)
    | AppliedForcedPattern (Pat Relevance)
    deriving Show

data VerFailure = VerFailure VerError [String]
type Ver a = ReaderT (VerTraceback, Ctx Relevance) (Except VerFailure) a
type VerTraceback = [String]

type Term = TT Relevance
type Type = TT Relevance

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
    [ "  "
        ++ show defName
        ++ " " ++ show (prettyCol defR)
        ++ " " ++ show defType
    | Def{defName, defR, defType} <- M.elems ctx
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
mustBeType ty = conv ty (V typeOfTypes)

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
verDef (Def n r ty (Abstract _)) = bt ("DEF-ABSTR", n) $ do
    tyty <- verTm E ty
    mustBeType tyty

verDef d@(Def n r ty (Term tm)) = bt ("DEF-TERM", n) $ do
    tyty <- verTm E ty
    mustBeType tyty
    tmty <- with d{ defBody = Abstract Var } $ verTm r tm
    conv tmty ty

verDef d@(Def n r ty (Clauses cls)) = bt ("DEF-CLAUSES", n) $ do
    tyty <- verTm E ty
    mustBeType tyty
    with d{ defBody = Abstract Var } $
        mapM_ (verClause r) cls

verClause :: Relevance -> Clause Relevance -> Ver ()
verClause r (Clause pvs lhs rhs) = bt ("CLAUSE", lhs) $ do
    -- check patvars
    ctx <- getCtx
    let pvsN = S.fromList (map defName pvs)
    patN <- case freePatVars ctx lhs of
        Just pvs -> return pvs
        Nothing  -> verFail $ NonLinearPattern lhs

    if pvsN /= patN
        then verFail $ PatvarsPatternMismatch (S.toList pvsN) (S.toList patN)
        else return ()

    verDefs pvs
    lhsTy <- verPat True r r (M.fromList [(defName d, d) | d <- pvs]) lhs
    withs pvs $ do
        rhsTy <- verTm r rhs
        conv lhsTy rhsTy

verTm :: Relevance -> Term -> Ver Type
verTm E (V n) = bt ("VAR-E", n) $ do
    d <- lookupName n
    return $ defType d

verTm R (V n) = bt ("VAR-R", n) $ do
    d <- lookupName n
    defR d <-> R
    return $ defType d

verTm r (Bind Lam [d@(Def n s ty (Abstract Var))] tm) = bt ("LAM", r, n) $ do
    tyty <- verTm E ty    
    mustBeType tyty
    tmty <- with d $ verTm r tm
    return $ Bind Pi [d] tmty

verTm r (Bind Pi [d@(Def n s ty (Abstract Var))] tm) = bt ("PI", r, n) $ do
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
        Bind Pi [Def n piR piTy (Abstract Var)] piRhs -> do
            piR <-> s
            xty <- verTm (r /\ s) x
            conv xty piTy            
            return $ subst n x piRhs

        _ -> verFail $ NotPi fty

verTm r tm = bt ("UNKNOWN-TERM", tm) $ do
    verFail NotImplemented

-- The Bool says whether an applied [forced pattern] is allowed to occur.
-- The only case where it is allowed is the name of the function.
verPat :: Bool -> Relevance -> Relevance -> Ctx Relevance -> Pat Relevance -> Ver Type
verPat fapp funR r pvs (PV n)
    | Just d <- M.lookup n pvs
    = bt ("PAT-VAR", n) $ do
        defR d <-> r
        return $ defType d

verPat fapp funR r pvs (PV n) = bt ("PAT-REF", n) $ do
    d <- lookupName n

    -- since it's not a patvar, it must be a constructor
    case defBody d of
        Abstract Constructor -> return ()
        _ -> verFail $ NotConstructor n

    -- all unforced constructors inspect unconditionally
    funR --> r
    funR --> defR d

    return $ defType d

verPat fapp funR r pvs (PApp s f x) = bt ("PAT-APP", fapp, r, s, f, x) $ do
    ctx <- getCtx

    case f of
        PForced tm
            | (V n, _args) <- unApply tm
            , Just cd@(defBody -> Abstract Constructor) <- M.lookup n ctx
            -> r --> defR cd  -- forced constructor

        PHead f  -- whole fun def will be var at this stage
            | Just (defBody -> Abstract Var) <- M.lookup f ctx
            , fapp  -- can appear here
            -> return ()

        PV n
            | Just (defBody -> Abstract Constructor) <- M.lookup n ctx
            -> return () -- regular constructor

        PApp _ _ _ -> return ()

        _ -> verFail $ BadPatAppHead f

    fty <- verPat fapp funR r pvs f
    case whnf ctx fty of
        Bind Pi [Def n piR piTy (Abstract Var)] piRhs -> do
            piR <-> s
            xty <- verPat False funR (r /\ s) pvs x
            with' (M.union pvs) $
                conv xty piTy
            return $ subst n (pat2term x) piRhs

        _ -> verFail $ NotPi fty

verPat fapp funR r pvs (PForced tm) = bt ("PAT-FORCED", tm) $ do
    with' (M.union pvs) $ do
        verTm r tm

verPat fapp funR r pvs (PHead f) = bt ("PAT-HEAD", f) $ do
    d <- lookupName f
    case defBody d of
        Abstract Var -> return ()  -- recursive refs are abstract
        _ -> verFail $ NotClauses f

    funR --> defR d

    return $ defType d

conv :: Type -> Type -> Ver ()
conv p q = do
    ctx <- getCtx
    conv' (whnf ctx p) (whnf ctx q)
    
conv' :: Type -> Type -> Ver ()
conv' (V n) (V n')
    | n == n' = return ()

conv' (App I f x) (App I f' x') = bt ("CONV-APP-IRR", f, x, f', x') $ do
    conv f f'

conv' (App r f x) (App r' f' x') = bt ("CONV-APP", f, x, f', x') $ do
    r <-> r'
    conv f f'
    conv x x'

conv'
    (Bind b  [d@(Def  n  r  ty  (Abstract Var))] tm)
    (Bind b' [d'@(Def n' r' ty' (Abstract Var))] tm')
    | b == b' = bt ("CONV-BIND", b, d, tm, d', tm') $ do
        r <-> r'
        conv ty ty'
        with d $ 
            conv tm (subst n' (V n) tm')

{- This would be necessary for conversion-checking of multilets. Let's disable them for now.
conv' (Bind b (d:ds) tm) (Bind b' (d':ds') tm')
    = bt ("CONV-SIMPL", b) $
        conv' (Bind b [d] $ Bind b ds tm) (Bind b' [d'] $ Bind b' ds' tm')
-}

conv' p q = verFail $ CantConvert p q
