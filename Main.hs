module Main where

import TTstar
import Erasure.Meta
import Erasure.Check
import Erasure.Solve
import Erasure.Prune

import qualified Data.Set as S

infixr 3 ~>
(~>) :: TT -> TT -> TT
(~>) = Bind Pi Nothing "_"

infixr 3 .->
(.->) :: (String, TT) -> TT -> TT
(n, ty) .-> tm = Bind Lam Nothing n ty tm

infixl 4 !
(!) :: TT -> TT -> TT
(!) = App Nothing

int :: TT
int = C TInt

testTerm :: TT
testTerm = ("x", int) .-> V "x"

testProg :: Program (Maybe Relevance)
testProg = Prog
    [ Def Nothing "id" intFun
        $ Fun (("y", int) .-> V "y")
    , Def Nothing "const_42" intFun
        $ Fun (("x", int) .-> C (Int 42))
    , Def Nothing "f" (intFun ~> int ~> intFun ~> int ~> int)
        $ Fun (
            ("g", intFun) .->
              ("z", int) .->
                ("h", intFun) .->
                  ("w", int) .->
                    Prim Plus ! (V "g" ! V "z") ! (V "h" ! V "w")
          )
    , Def (Just R) "main" (int)
        $ Fun (V "f" ! V "id" ! C (Int 3) ! V "const_42" ! C (Int 7))
    --    $ Fun (V "id" ! C (Int 42))
    ]
  where
    intFun = int ~> int

main :: IO ()
main = do
    putStrLn "### Metaified ###"
    let metaified = meta testProg
    print metaified
    putStrLn "### Constraints ###"
    let cs = either (error . show) id . check $ metaified
    mapM_ print $ S.toList cs
    putStrLn ""
    putStrLn "### Solution ###"
    let uses = solve cs
    print $ S.toList uses
    putStrLn ""
    putStrLn "### Annotated ###"
    let annotated = annotate uses $ metaified
    print $ annotated
    putStrLn "### Pruned ###"
    let pruned = prune annotated
    print $ pruned
