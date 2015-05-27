module Main where

import TT
import Parser
import Explorer
import Whnf
import Eval

import Util.PrettyPrint

import Erasure.Meta
import Erasure.Check
import Erasure.Solve
import Erasure.Prune

import Control.Applicative
import Text.Parsec
import System.Environment
import qualified Data.Set as S
import qualified Data.Map as M

-- for every function f
--   for every argument i
--     if (Exists j. USED_f_i_j)
--       we can't erase the argument completely
--       but we can replace it with NULL whenever USED_f_i_j is False
--     otherwise
--       we can erase f_i completely
--
-- constraints are part of type signature
--
-- we copy a fresh set of constraints whenever the function is applied
--  unless it's recursive
--
-- how do we deal with self-referential functions? (probably don't copy the constraint set)
--   -> rules out erasure-polymorphic recursion (that's fair because the annotations are completely inferred)
--   -> maybe we could give the user a chance to explicitly annotate polymorphic recursion and then just check it
--
-- interactive constraint explorer
--
-- ***
--
-- this is too whole-program (because constructor usage can only be determined by whole-program analysis)
-- however, every function has 1. type, 2. erasure constraints
--  -> these are (of course) computed in isolation
-- so it's questionable whether we should call it whole-program analysis
-- (the information is usable on its own)
--
-- ***
--
-- A meta on a Pi is the upper bound of all Lambdas typed by that Pi.
-- We could add another meta to every Pi, which is the lower bound of all Lams typed by it.
-- Then we could tell whether *all* lambdas are relevant or whether some are irrelevant.
--
-- => therefore we can annotate every binder with the supremum and infimum of their variables
--    and erase accordingly
-- => lambdas imply pis (one pi might type multiple lambdas (case branches) but not vice versa)
--
-- Flow of relevance:
--  - variables always start as relevant at the tail of the term
--  - under an application, their relevance is and-ed with relevance of the lambda
--  - finally, they die in their binder
--
-- We probably should perform the duplication in (checkTerm $ V n) -- because only variables can be duplicated.
--
-- ***
--
-- ifl : python backend
-- pldi : erasure
-- meetings every other tuesday afternoon starting with 19.5.2015
--
-- ***
--
-- general rule:
-- we always assume we're in a completely relevant environment
-- the environment will insert conditions using "cond" if that's not the case but we mustn't care about this


main :: IO ()
main = do
    [fname] <- getArgs
    code <- readFile fname
    case parse ttProgram fname code of
        Left e -> print e
        Right prog -> do
            putStrLn "-- vim: ft=agda"
            putStrLn ""
            putStrLn "### Desugared ###\n"
            printP prog

            putStrLn "### Metaified ###\n"
            let metaified = meta prog
            printP metaified

            putStrLn "### Inferred definitions ###\n"
            let (ctx, cs) = either (error . show) id . check $ metaified
            mapM_ (putStrLn . fmtCtx) $ M.toList ctx
            putStrLn ""

            putStrLn "### Constraints ###\n"
            mapM_ (putStrLn . fmtCtr) $ M.toList cs
            putStrLn ""

            putStrLn "### Solution ###\n"
            let (uses, residue) = solve cs
            print $ S.toList uses
            genHtml (fname ++ ".html") metaified cs uses
            putStrLn ""

            case Fixed E `S.member` uses of
                True -> putStrLn "!! inconsistent annotation"
                False -> do
                    putStrLn "### Annotated ###\n"
                    let annotated = annotate uses $ metaified
                    printP $ annotated

                    putStrLn "### Pruned ###\n"
                    let pruned = prune annotated
                    printP $ pruned

                    putStrLn "### Normal forms ###\n"
                    putStrLn "unerased:"
                    putStrLn $ "  " ++ show (eval NF prog)
                    putStrLn "erased:"
                    putStrLn $ "  " ++ show (eval NF pruned)
  where
    fmtCtr (gs,cs) = show (S.toList gs) ++ " -> " ++ show (S.toList cs)
    fmtCtx (n, (Def _n r ty mtm Nothing)) = prettyShow (n, r, ty)
    fmtCtx (n, (Def _n r ty mtm (Just cs))) = prettyShow (n, r, ty) ++ "\n"
        ++ unlines (map (("  " ++) . fmtCtr) $ M.toList cs)

