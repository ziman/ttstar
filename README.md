## TTstar

### Features

Besides what the original paper had, we have:
* higher-order erasure
* changing arities of functions
* data constructor support

### TODO
* erasure polymorphism
* good error reporting

### Secondary features
* erasure explorer
* including very dependent functions
* erasure of whole functions (dead function removal)
* recursion

### Questions
* erasure-elaboration without typechecking + conversion + matching
* representation of the subset of 2^n relevance levels in the type
    * explicit: all combinations
    * implicit: constraints
    * partial explicit: only combinations of non-R-fixed args
* `Bind Pat` is a better representation of `ConCase`
