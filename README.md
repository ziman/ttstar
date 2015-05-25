## TTstar

### Features

Besides what the original paper had, we have:
* higher-order erasure
* changing arities of functions
* data constructor support
* erasure polymorphism for let-bound names
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
