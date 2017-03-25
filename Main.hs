{-# LANGUAGE FlexibleContexts #-}
module Main where

import TT
import TTLens
import Parser
import Normalise

import Args (Args)
import qualified Args

import Codegen.Common
import qualified Codegen.Scheme

import Util.PrettyPrint

import Erasure.Evar
import Erasure.Infer
import Erasure.Solve
import Erasure.Annotate
import Erasure.Specialise
import Erasure.Prune
import Erasure.Verify

import Control.Monad
import qualified Data.Set as S
import qualified Data.Map as M

import Lens.Family2

pipeline :: Args -> IO ()
pipeline args = do
    when (Args.verbose args) $
        putStrLn "-- vim: ft=idris"

    let sourceFname = Args.sourceFile args
    code <- readFile sourceFname
    prog <- case parseProgram sourceFname code of
        Left e -> do
            print e
            error "parse error"

        Right prog ->
            return prog

    -- evarify the program
    let evarified_1st = evar prog

    when (Args.verbose args) $ do
        putStrLn ""
        putStrLn "### Desugared ###"
        print prog
        putStrLn ""

        putStrLn "### Evarified ###"
        print evarified_1st
        putStrLn ""

    let iterSpecialisation evarified = do
            uses <- case Args.skipInference args of
                True -> return $ S.fromList (
                    evarified_1st ^.. (ttRelevance :: Traversal' (TT Evar) Evar)
                  )
                False -> do
                    let cs = either (error . show) id . infer $ evarified
                    when (Args.verbose args) $ do
                        putStrLn "### Constraints ###\n"
                        mapM_ (putStrLn . fmtCtr) $ M.toList cs
                        putStrLn ""

                    let (uses, _residue) = solve cs
                    when (Args.verbose args) $ do
                        putStrLn "### Solution ###\n"
                        print $ S.toList uses
                        putStrLn ""

                    return uses

            if Fixed E `S.member` uses
                then error "!! inconsistent annotation"
                else return ()

            let annotated = annotate uses $ evarified
            when (Args.verbose args) $ do
                putStrLn "### Annotated ###"
                print annotated
                putStrLn ""

            let specialised = specialise evarified annotated
            when (Args.verbose args) $ do
                putStrLn "### Specialised ###"
                print specialised
                putStrLn ""

            if evarsOccurIn specialised
                then iterSpecialisation specialised
                else return annotated  -- fixed point reached

    annotated <- iterSpecialisation evarified_1st

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
    when (Args.verbose args) $ do
        putStrLn "### Pruned ###"
        print pruned
        putStrLn ""

    case Args.dumpPretty args of
        Nothing -> return ()
        Just fname -> writeFile fname $ show pruned ++ "\n"

    when (not $ Args.skipEvaluation args) $ do
        let unerasedNF = red NF (builtins $ Just relOfType) prog
        let erasedNF = red NF (builtins ()) pruned
        when (Args.verbose args) $ do
            putStrLn "### Normal forms ###\n"
            putStrLn "unerased:"
            putStrLn $ "  " ++ show unerasedNF
            putStrLn ""
            putStrLn "erased:"
            putStrLn $ "  " ++ show erasedNF
            putStrLn ""

    case Args.dumpScheme args of
        Nothing -> return ()
        Just fname -> do
            let code = render "; " (cgRun Codegen.Scheme.codegen pruned) ++ "\n"
            writeFile fname code
  where
    fmtCtr (gs,cs) = show (S.toList gs) ++ " -> " ++ show (S.toList cs)


main :: IO ()
main = pipeline =<< Args.parse
