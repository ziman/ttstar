#!/bin/bash

# Racket
scheme_racket() {
    racket -r $1.scm > $1.scm.out
}

# Chicken Scheme, interpreter
scheme_csi() {
    csi -qb "$1".scm > $1.scm.out
}

# Chicken Scheme, compiler
scheme_csc() {
    csc "$1".scm
    "$1" > "$1".scm.out
    rm -f "$1"
}

scheme() {
    scheme_csi "$@"
}

for i in examples/*.tt; do
    n=${i%.tt}
    echo $i
    ./ttstar $i > $n.out 2>&1 \
        && scheme $n
done
