module Main where

import Args (Args, Solver(..))
import qualified Args

import TT.Core
import TT.Lens
import TT.Utils
import TT.Parser
import TT.Normalise

import IR.FromTT
import IR.Pretty ()

import qualified Codegen.Scheme
import qualified Codegen.SchemeIR
import qualified Codegen.Malfunction

import Util.PrettyPrint

import Erasure.Evar
import Erasure.Infer
import Erasure.Annotate
import Erasure.Specialise
import Erasure.Prune
import Erasure.Verify

import Solver.Simple
import Solver.Graph
import Solver.Indexed
import Solver.LMS

import TT.Elab

import qualified Optimisation.Identity

import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.IntSet as IS

import Lens.Family2

pipeline :: Args -> IO ()
pipeline args = do
    when (Args.verbose args) $
        putStrLn "-- vim: ft=ttstar"

    let sourceFname = Args.sourceFile args
    progMeta <- readProgram sourceFname >>= \case
        Left  err  -> print err >> error "parse error"
        Right prog -> return prog

    when (Args.verbose args) $ do
        putStrLn ""
        putStrLn "### Desugared ###"
        print progMeta

    -- elaborate metas
    prog <- case elab progMeta of
        Left err -> putStrLn err >> error "elaboration failed"
        Right prog -> return prog

    when (Args.verbose args) $ do
        putStrLn ""
        putStrLn "### Elaborated ###"
        print prog

    -- evarify the program
    let evarified_1st = evar prog

    when (Args.verbose args) $ do
        putStrLn ""
        putStrLn "### Evarified ###"
        print evarified_1st

        putStrLn ""

    let iterSpecialisation evarified = do
            (evarified, uses) <- case Args.skipInference args of
                True -> return
                    ( evarified
                    , S.fromList $ evarified_1st ^.. (
                            ttRelevance :: Traversal' (TT Evar) Evar
                        )  -- all annotations are used
                    )

                False -> do
                    -- map evars to their connected components

                    -- We don't have a graph reductor (yet)
                    -- and it turns out that using `id` is actually better
                    -- than using the dumb reductor.
                    --
                    -- This is not surprising because `main` is a definition
                    -- and it will be reduced by inference, which of course
                    -- amounts to running the (dumb) solver on the whole program.
                    --
                    -- This also means that if we have a reductor,
                    -- the solver has nothing to do.
                    let redConstrs =
                            case Args.solver args of
                                Simple  -> Solver.Simple.reduce
                                Graph   -> id
                                Indexed -> Solver.Indexed.reduce
                                LMS     -> Solver.LMS.reduce

                    let Constrs impls
                            = either (error . show) id
                            . infer redConstrs
                            $ evarified

                    when (Args.verbose args) $ do
                        putStrLn "### Constraints ###\n"
                        mapM_ (putStrLn . fmtCtr) $ M.toList impls
                        putStrLn ""

                    let uses = solveConstraints impls

                    when (Args.verbose args) $ do
                        putStrLn "### Solution ###\n"
                        print $ S.toList uses
                        putStrLn ""

                    return (evarified, uses)

            if Fixed E `S.member` uses
                then error "!! inconsistent annotation"
                else return ()

            let annotated = annotate uses $ evarified
            when (Args.verbose args) $ do
                putStrLn "### Annotated ###"
                print annotated
                putStrLn ""

            case Args.skipSpecialisation args of
                True -> return annotated
                False -> do
                    let specialised = specialise evarified annotated
                    when (Args.verbose args) $ do
                        putStrLn "### Specialised ###"
                        print specialised
                        putStrLn ""

                    if evarsOccurIn specialised
                        then iterSpecialisation specialised
                        else return annotated  -- fixed point reached

    annotated_raw <- case Args.skipSpecialisation args of
        False -> iterSpecialisation evarified_1st
        True -> iterSpecialisation $ monomorphise evarified_1st

    annotated <- case Args.skipInference args of
        False -> return annotated_raw
        True -> ttRelevance setToR annotated_raw
                -- specialisation may have created evars which we want to set to R

    when (Args.verbose args) $ do
        putStrLn "### Final annotation ###"
        print annotated
        putStrLn ""

    when (not $ Args.skipVerification args) $ do
        when (Args.verbose args) $
            putStrLn "### Verification ###\n"
        case verify annotated of
            Left err -> error $ "!! verification failed: " ++ show err
            Right () -> when (Args.verbose args)
                            $ putStrLn "Verification successful.\n"

    let pruned = pruneTm annotated -- specialised
    when (Args.verbose args && not (Args.optIdentity args)) $ do
        putStrLn "### Pruned ###"
        print pruned
        putStrLn ""

    let optimised
            | Args.optIdentity args = Optimisation.Identity.optimise pruned
            | otherwise = pruned

    when (Args.verbose args && Args.optIdentity args) $ do
        putStrLn "### Optimised ###"
        print optimised
        putStrLn ""

    let optimisedIR = toIR optimised
    when (Args.verbose args) $ do
        putStrLn "### Intermediate representation ###\n"
        print optimisedIR
        putStrLn ""

    case Args.dumpPretty args of
        Nothing -> return ()
        Just fname -> dumpTT fname optimised

    case Args.dumpIR args of
        Nothing -> return ()
        Just fname -> dumpTT fname optimisedIR

    case Args.dumpScheme args of
        Nothing -> return ()
        Just fname -> dumpScheme fname optimised

    case Args.dumpSchemeIR args of
        Nothing -> return ()
        Just fname -> dumpSchemeIR fname optimisedIR

    case Args.dumpMalfunction args of
        Nothing -> return ()
        Just fname -> dumpMalfunction fname optimisedIR

    case Args.dumpStats args of
        Nothing -> return ()
        Just fname -> do
            let annotations = evarified_1st ^.. (ttRelevance :: Traversal' (TT Evar) Evar)
            writeFile fname $ unlines
                [ "{ \"annotations\": " ++ show (length annotations)
                , ", \"evars\": " ++ show (IS.size $ IS.fromList [i | EV i <- annotations])
                , ", \"annotations_used\": " ++ (show . length . filter (== R)) (
                        annotated ^.. (ttRelevance :: Traversal' (TT Relevance) Relevance)
                    )
                , "}"
                ]

    let unerasedNF = red NF (builtins $ Just relOfType) prog
    let erasedNF = red NF (builtins ()) optimised

    when (Args.verbose args) $ do
        when (not $ Args.skipEvaluation args) $ do
            putStrLn "### Normal forms ###\n"
            putStrLn "unerased:"
            putStrLn $ "  " ++ show unerasedNF
            putStrLn ""
            putStrLn "erased:"
            putStrLn $ "  " ++ show erasedNF
            putStrLn ""

    case Args.dumpNF args of
        Nothing -> return ()
        Just fname -> dumpTT fname erasedNF

    case Args.dumpNFScheme args of
        Nothing -> return ()
        Just fname -> dumpScheme fname erasedNF
  where
    fmtCtr (gs,cs) = show (S.toList gs) ++ " -> " ++ show (S.toList cs)
    dumpTT fname prog = writeFile fname $ "-- vim: ft=ttstar\n" ++ show prog ++ "\n"
    dumpScheme fname prog = writeFile fname $ render "; " (Codegen.Scheme.codegen prog) ++ "\n"
    dumpMalfunction fname prog = writeFile fname $ render "; " (Codegen.Malfunction.codegen prog) ++ "\n"

    dumpSchemeIR fname prog = do
        rts <- readFile $ Args.rtsSchemePath args
        writeFile fname $ rts ++ "\n" ++ render "; " (Codegen.SchemeIR.codegen prog) ++ "\n"

    solveConstraints = case Args.solver args of
        Simple  -> fst . Solver.Simple.solve
        Graph   -> Solver.Graph.solve
        Indexed -> fst . Solver.Indexed.solve
        LMS     -> fst . Solver.LMS.solve

    setToR I = return I  -- preserve irrelevance
    setToR _ = return R

main :: IO ()
main = pipeline =<< Args.parse
