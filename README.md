## TTstar

### Features

Besides what the original paper had, we have:
* [P] higher-order erasure
* [P] changing arities of functions
* [M] data constructor support
    * because M-L avoids case-expressions
* [MP] erasure polymorphism for let-bound names (includes top-level)
    * but not lambda-bound names
* pruning LHSs of clauses
* irrelevant clause removal
* local pattern-matching clauses in let
    * only one definition per let at the moment; absolutely not necessary, I just can't be bothered to invent good syntax for it

[P] = improvement over previous paper, [M] = improvement over Mishra-Linger


### TODO
* good error reporting
* first-order evars for unlimited-rank polymorphism

### Secondary features
* erasure explorer
* including very dependent functions
* erasure of whole functions (dead function removal)
* recursion
* `ConCase` represented with `Bind Pat`
