module Main where

import TT
import Parser
import Explorer

import Erasure.Meta
import Erasure.Check
import Erasure.Solve
import Erasure.Prune

import Control.Applicative
import Text.Parsec
import System.Environment
import qualified Data.Set as S

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

main :: IO ()
main = do
    [fname] <- getArgs
    code <- readFile fname
    case parse (sp *> parseProg <* eof) fname code of
        Left e -> print e
        Right prog -> do
            putStrLn "-- vim: ft=agda"
            putStrLn ""
            putStrLn "### Desugared ###\n"
            print prog
            putStrLn "### Metaified ###\n"
            let metaified = meta prog
            print metaified
            putStrLn "### Constraints ###\n"
            let cs = either (error . show) id . check $ metaified
            mapM_ print $ S.toList cs
            putStrLn ""
            putStrLn "### Solution ###\n"
            let uses = solve cs
            print $ S.toList uses
            genHtml (fname ++ ".html") metaified cs uses
            putStrLn ""
            putStrLn "### Annotated ###\n"
            let annotated = annotate uses $ metaified
            print $ annotated
            putStrLn "### Pruned ###\n"
            let pruned = prune annotated
            print $ pruned
