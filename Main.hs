module Main where

import TTstar
import Erasure.Meta
import Erasure.Check
import Erasure.Solve
import Erasure.Prune

import qualified Data.Set as S

infixr 3 ~~>
(~~>) :: TT -> TT -> TT
(~~>) = Bind Pi Nothing "_"

infixr 3 -->
(-->) :: (Name, TT) -> TT -> TT
(n, ty) --> tm = Bind Pi Nothing n ty tm

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

typ :: TT
typ = C TType

testProg :: Program (Maybe Relevance)
testProg = Prog
    [ Def Nothing "Bool" typ Ctor
    , Def Nothing "True" (V "Bool") Ctor
    , Def Nothing "False" (V "Bool") Ctor
    , Def Nothing "Maybe" (typ ~~> typ) Ctor
    , Def Nothing "Nothing" (("a", typ) --> V "Maybe" ! V "a") Ctor
    , Def Nothing "Just" (("a", typ) --> ("x", V "a") --> V "Maybe" ! V "a") Ctor
    , Def Nothing "id" intFun
        $ Fun (("y", int) .-> V "y")
    , Def Nothing "const_42" intFun
        $ Fun (("x", int) .-> C (Int 42))
    , Def Nothing "f" (intFun ~~> int ~~> intFun ~~> int ~~> int)
        $ Fun (
            ("g", intFun) .->
              ("z", int) .->
                ("h", intFun) .->
                  ("w", int) .->
                    Prim Plus ! (V "g" ! V "z") ! (V "h" ! V "w")
          )
    , Def Nothing "boolTy" (V "Bool" ~~> typ)
        $ Fun (("x", V "Bool") .->
                (Case (V "x")
                    [ ConCase "True" Nothing [] (V "Bool")
                    , ConCase "False" Nothing [] int
                    ]))
    , Def Nothing "retTy" (("x", V "Maybe" ! V "Bool") --> typ)
        $ Fun (("x", V "Maybe" ! V "Bool") .->
                 (Case (V "x")
                    [ ConCase "Just" Nothing ["b"] (V "boolTy" ! V "b")
                    , DefaultCase typ
                    ]))
    , Def Nothing "depF" (("x", V "Maybe" ! V "Bool") --> V "retTy" ! V "x")
        $ Fun (("x", V "Maybe" ! V "Bool") .->
                (Case (V "x")
                    [ ConCase "Just" Nothing ["b"]
                        (Case (V "b")
                            [ ConCase "True" Nothing [] (V "False")
                            , ConCase "False" Nothing [] (C $ Int 42)
                            ])
                    , ConCase "Nothing" Nothing [] int
                    ]))
    , Def (Just R) "main" int
        $ Fun (V "depF" ! (V "Just" ! V "False"))  -- very dependent
--        $ Fun (V "f" ! V "id" ! C (Int 3) ! V "const_42" ! C (Int 7))  -- higher-order erasure
    ]
  where
    intFun = int ~~> int

main :: IO ()
main = do
    putStrLn "### Original program ###\n"
    print testProg
    putStrLn "### Metaified ###\n"
    let metaified = meta testProg
    print metaified
    putStrLn "### Constraints ###\n"
    let cs = either (error . show) id . check $ metaified
    mapM_ print $ S.toList cs
    putStrLn ""
    putStrLn "### Solution ###\n"
    let uses = solve cs
    print $ S.toList uses
    putStrLn ""
    putStrLn "### Annotated ###\n"
    let annotated = annotate uses $ metaified
    print $ annotated
    putStrLn "### Pruned ###\n"
    let pruned = prune annotated
    print $ pruned
