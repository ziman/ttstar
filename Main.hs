module Main where

import TTstar
import Erasure

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

testProg :: Program TT
testProg =
    [ Fun
      { dName = "const_42"
      , dType = intFun
      , dBody = "x" .-> C (Int 42)
      }
    , Fun
      { dName = "id"
      , dType = intFun
      , dBody = "x" .-> V "x"
      }
    , Fun
      { dName = "f"
      , dType = intFun ~> C TInt ~> intFun ~> C TInt ~> C TInt
      , dBody = "g" .-> "x" .-> "h" .-> "y" .-> Prim Plus ! (V "g" ! V "x") ! (V "h" ! V "y")
      }
    , Fun
      { dName = "main"
      , dType = C TInt
      , dBody = V "f" ! V "id" ! C (Int 3) ! V "const_42" ! C (Int 7)
      }
    ]
  where
    intFun = C TInt ~> C TInt

main :: IO ()
main = do
    print $ testProg
