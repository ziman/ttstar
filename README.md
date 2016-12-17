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
