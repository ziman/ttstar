module Main where

import TTstar
import Erasure
import Erasure.Meta
import Erasure.Check
import Erasure.Solve
import Erasure.Prune

import qualified Data.Set as S

infixr 3 ~>
(~>) :: TT -> TT -> TT
(~>) = Bind Pi Nothing "_"

infixr 3 .->
(.->) :: String -> TT -> TT
n .-> tm = Bind Lam Nothing n (C TInt) tm

infixl 4 !
(!) :: TT -> TT -> TT
(!) = App Nothing

testTerm :: TT
testTerm = "x" .-> V "x"

testProg :: Program (Maybe Relevance)
testProg = Prog
    [ Def Nothing "const_42" intFun
        $ Fun ("x" .-> C (Int 42))
    , Def Nothing "id" intFun
        $ Fun ("y" .-> V "y")
    , Def Nothing "f" (intFun ~> C TInt ~> intFun ~> C TInt ~> C TInt)
        $ Fun ("g" .-> "z" .-> "h" .-> "w" .-> Prim Plus ! (V "g" ! V "z") ! (V "h" ! V "w"))
    , Def (Just R) "main" (C TInt)
        $ Fun (V "f" ! V "id" ! C (Int 3) ! V "const_42" ! C (Int 7))
    ]
  where
    intFun = C TInt ~> C TInt

main :: IO ()
main = do
    putStrLn "-- Constraints --"
    let cs = fromRight . check $ meta testProg
    mapM_ print $ S.toList cs
    putStrLn ""
    putStrLn "-- Solution --"
    let uses = solve cs
    print $ S.toList uses
    putStrLn ""
    putStrLn "-- Annotated --"
    let annotated = annotate uses $ meta testProg
    print $ annotated
  where
    fromRight (Right x) = x
