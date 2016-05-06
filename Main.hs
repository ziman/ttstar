{-# LANGUAGE FlexibleContexts #-}
module Main where

import TT
{-
import TTLens
import Parser
import Pretty
import Explorer
import Normalise
import Eval
-}

import Util.PrettyPrint

{-
import Erasure.Meta
import Erasure.Check
import Erasure.Solve
import Erasure.Annotate
import Erasure.Specialise
import Erasure.Prune
import Erasure.Verify
-}

import Lens.Family2

import Control.Applicative
import Text.Parsec
import System.Environment
import qualified Data.Set as S
import qualified Data.Map as M

{- Questions for Edwin:
 - * is evaluation per-clause okay with forced patterns?
 - * prune is no longer trivial. Is that okay?
 -}

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
--
--  ***
--
--  Relevance levels
--
--    E < N < R   |   < I ?
--
--  Constraints:
--
--    (r, E) --> (r, R)
--
--  Solver:
--
--    1. keep a map of assignments (r --> E)
--    2. initialise the map so that every `r` maps to `E` at first
--    3. go round'n'round the constraints and update the mapping
--
--  Tradeoff:
--
--    Smarter constraints:
--      -> more complicated solver
--      -> fewer constraints


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

{-
            putStrLn "### Metaified ###\n"
            let metaified = meta prog
            printP metaified

            let iterSpecialisation metaified = do
                    putStrLn "### Inferred definitions ###\n"
                    let (ctx, cs) = either (error . show) id . check $ metaified
                    mapM_ (putStrLn . fmtCtx) $ M.toList ctx
                    putStrLn ""

                    putStrLn "### Constraints ###\n"
                    mapM_ (putStrLn . fmtCtr) $ M.toList (runCS cs)
                    putStrLn ""

                    putStrLn "### Solution ###\n"
                    let (uses, residue) = solve cs
                    print $ S.toList uses
                    -- genHtml (fname ++ ".html") metaified cs uses
                    putStrLn ""

                    if Fixed E `S.member` uses
                    then error "!! inconsistent annotation"
                    else return ()

                    putStrLn "### Annotated ###\n"
                    let annotated = annotate uses $ metaified
                    printP $ annotated

                    putStrLn "### Specialised ###\n"
                    let specialised = specialise metaified annotated
                    printP $ specialised

                    -- TODO: check for useless pattern columns
                    -- no vars bound, same ctor (could be nested inside other ctors)
                    --
                    -- separate pattern fragment?
                    -- + separate typechecker for patterns?
                    --
                    -- + perhaps separate verification checker?

                    if ndefs specialised == ndefs annotated
                        then return annotated  -- fixed point reached
                        else iterSpecialisation specialised

            annotated <- iterSpecialisation metaified

            putStrLn "### Final annotation ###\n"
            -- let annotated = annotate S.empty specialised  -- no usage set needed, everything is Fixed
            printP $ annotated

            putStrLn "### Verification ###\n"
            case verify annotated of
                Left err -> error $ "!! verification failed: " ++ show err
                Right () -> putStrLn "Verification successful.\n"

            putStrLn "### Pruned ###\n"
            let pruned = prune annotated -- specialised
            printP $ pruned

            putStrLn "### Normal forms ###\n"
            putStrLn "unerased:"
            putStrLn $ "  " ++ show (eval NF (builtins $ Just R) prog)
            putStrLn "erased:"
            putStrLn $ "  " ++ show (eval NF (builtins ()) pruned)
  where
    fmtCtr (gs,cs) = show (S.toList gs) ++ " -> " ++ show (S.toList cs)

    fmtCtx (n, (Def _n r ty body Nothing))
        = prettyShow (Def n r ty body Nothing) ++ "\n"

    fmtCtx (n, (Def _n r ty body (Just (CS cs))))
        = prettyShow (Def n r ty body Nothing) ++ "\n"
        ++ unlines (map (("  " ++) . fmtCtr) $ M.toList cs)

    ndefs (Prog defs) = length defs
-}
