#!/bin/bash

set -o pipefail

die() {
    echo "$@"
    exit 1
}

# Racket
scheme_racket() {
    racket -r $1.scm > $1.scm.out
    racket -r "$1"-unerased.scm > $1-unerased.scm.out
}

# Chicken Scheme, interpreter
scheme_csi() {
    csi -qb "$1".scm &> $1.scm.out
    csi -qb "$1"-unerased.scm &> $1-unerased.scm.out
}

# Chicken Scheme, compiler
scheme_csc() {
    csc "$1".scm
    csc "$1"-unerased.scm
    "$1" &> "$1".scm.out
    "$1"-unerased &> "$1"-unerased.scm.out
    rm -f "$1" "$1"-unerased
}

# Here, select which compiler you want to use.
scheme() {
    scheme_csi "$@"
}

install() {
    chicken-install matchable
    # pattern matching is in racket base already
}

cabal install -j1 \
    || die "could not install"

for i in examples/*.tt; do
    n=${i%.tt}

    echo $i
    ./ttstar $i > $n.out 2>&1 \
        && scheme $n
done
