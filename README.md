## TTstar

### Features

Besides what the original paper had, we have the following
([P] = improvement over previous paper, [M] = improvement over Mishra-Linger):
* [P] higher-order erasure
* [P] changing arities of functions
* [M] data constructor support
    * because M-L avoids case-expressions
* [MP] erasure polymorphism for let-bound names
    * but not for lambda-bound names (would require extension of the type system)
    * probably equivalent to Hindley-Milner-style polymorphism


### TODO
* good error reporting
* first-order evars for unlimited-rank polymorphism

### Secondary features
* erasure explorer
* including very dependent functions
* erasure of whole functions (dead function removal)
* recursion
* `ConCase` represented with `Bind Pat`
