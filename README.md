# TTstar

Dependently typed core calculus with erasure inference.

## Features

### Erasure

* erasure inference (fills in erasure annotations)
* separate erasure checker (verifies consistency of inferred annotations)
* erasure from higher-order functions
* complete removal of unused arguments (rather than passing in `NULL`)
* erasure polymorphism for functions
* four constraint solvers
    * simple and straightforward O(n²) solver
    * graph-based constraint solver
    * indexing solver (fastest, default)
    * LMS solver
        * "last man standing"
        * Adapted from "Chaff: Engineering an efficient SAT solver"
          by Moskewicz et al., 2001.
        * theoretically faster than the indexer, my implementation is slower

### Language

* full dependent pattern matching clauses
* pattern matching local `let` definitions are useful for emulating
    * `case` expressions
    * `with` clauses
    * mutual recursion

### Practicalities

* type errors come with backtraces
* rudimentary FFI via `foreign` postulates
* a simplified intermediate representation for backends (`IR`)
    * translation from `TT` to `IR` compiles patterns into case trees
* native code generators
    * a codegen from `TT`: via Scheme (Chicken Scheme or Racket)
        * uses the `matchable` extension
    * a codegen from `IR`: produces standard Scheme
        * mostly R5RS-compliant
            * except that some programs redefine the same name repeatedly in `let*`
        * generated code runs much (~3x) faster when interpreted with `csi`
        * only about 10% faster than `TT`-generated code when compiled using `csc`

## Other stuff

* dependent erasure (if `x == 3` then `erased` else `not_erased`)
* unused functions are removed entirely
* `Refl` is always erased
* `Maybe` sometimes becomes Boolean after erasure

## Does not feature

* type inference
* mutual recursion
	* a restricted form is easy to achieve using local let bindings
	* sufficient in all cases I've come across
* much syntax sugar

<!--
Besides what the original paper had, we have:
* [M] support of inductive families and full dependent pattern matching
    * M-L avoids this entirely
* [MP] erasure polymorphism for let-bound names (includes top-level)
    * but not lambda-bound names
* checkable result of erasure
* an erasure calculus
* equivalence of pattern clauses vs. case trees
* pruning case trees
* local pattern-matching clauses in let
    * actually, let is fully equivalent to top-level
    * only one definition per let at the moment; absolutely not necessary, I just can't be bothered to invent good syntax for it
* separate typechecker that checks the result of inference

Symbols:
* [P] = improvement over previous paper, [M] = improvement over Mishra-Linger


### TODO
* good error reporting
* first-order evars for unlimited-rank polymorphism
* mutual recursion
    * this is fairly easy but it requires clumsy propagation of constraints
    * (iterate checking of Defs until the set of constraints does not change)
    * leave out of paper
    * if let f, g in X, then while checking body of f, we have empty set of constraints for g
    * therefore the reference to g in the body of f puts wrong constraints in
    * also implementable by non-mutual recursion with an extra tag argument

#### Short-term TODO
* fix mutual recursion in the implementation
    * then fix typing rules in the paper
* continue with the proofs in the paper
* This rule is disgustingly complicated but it just says "take all
known equalities and rewrite everything".
* Resolve telescopicness of lets. Let is not telescopic because it's
mutually recursive. Fix that.
* Probably nothing is telescopic in the Greek.

### Secondary features
* backtrace in typechecker
* erasure explorer (defunct)
* including very dependent functions
* erasure of whole functions (dead function removal)
* recursion
* every binder is a `Def`
* `Refl` is erased
-->
