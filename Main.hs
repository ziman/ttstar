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
--
-- how do we deal with self-referential functions? (probably don't copy the constrain set)
--   -> rules out erasure-polymorphic recursion (that's fair because the annotations are completely inferred)
--   -> maybe we could give the user a chance to explicitly annotate polymorphic recursion and then just check it

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
    {-
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
    -}
    , Def Nothing "apply" (("f", int ~~> int) --> int ~~> int)
        $ Fun (("f", int ~~> int) .-> ("x", int) .-> V "f" ! V "x")
    , Def (Just R) "main" int
        $ Fun (Prim Plus ! (V "apply" ! V "id" ! C (Int 3)) ! (V "apply" ! V "const_42" ! C (Int 7)))
--        $ Fun (V "depF" ! (V "Just" ! V "False"))  -- very dependent
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
