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
* erasure at `TT`, `LExp` and `DExp` levels

### How to do erasure polymorphism
* store separate per-definition dep graphs
* try to somehow reduce them
    * find things that must be `R`
    * find fixed things
    * from the things that don't have to be `R`, keep the dep graph (this will be small)
* copy them for every `V n` reference
* use upper+lower bounds to guide erasure
