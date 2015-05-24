## TTstar

### Features

Besides what the original paper had, we have:
* higher-order erasure
* changing arities of functions
* data constructor support
* erasure polymorphism for let-bound names
    * but not for lambda-bound names

### TODO
* good error reporting
* first-order evars for unlimited-rank polymorphism

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
* erasure at `TT`, `LExp` and `DExp` levels

### How to do erasure polymorphism
* store separate per-definition dep graphs
* try to somehow reduce them
    * find things that must be `R`
    * find fixed things
    * from the things that don't have to be `R`, keep the dep graph (this will be small)
    * there are also "inner" variables that relate the fun body to other functions -- nonreducible at this point (?)
        * or shall we run the solver after every definition?
        * yes, we will; that will replace most mvars with `R`, leaving just the meat
        * after every definition: reduce constraint set
            * for current definition
            * globally (because current definition may force some simplification in the global constraint set)
        * then duplication won't hurt much
* copy them for every `V n` reference
* use upper+lower bounds to guide erasure
