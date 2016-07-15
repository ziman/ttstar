## TTstar

### Features

Besides what the original paper had, we have:
* [P] higher-order erasure
* [P] changing arities of functions
* [P] dependent erasure (if `x == True` then erased else not erased)
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

[P] = improvement over previous paper, [M] = improvement over Mishra-Linger


### TODO
* good error reporting
* first-order evars for unlimited-rank polymorphism
* dead constructors (`Cuckoo`)

### Secondary features
* backtrace in typechecker
* erasure explorer
* including very dependent functions
* erasure of whole functions (dead function removal)
* recursion
* every binder is a `Def`
* `Refl` is erased
