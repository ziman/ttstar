#!/bin/bash

set -o pipefail

die() {
    echo "$@"
    exit 1
}

# Racket
scheme_racket() {
    racket -r "$1" $2 2>&1
}

# Chicken Scheme, interpreter
scheme_csi() {
    csi -qs "$1" $2 2>&1
}

# Chicken Scheme, compiler
scheme_csc() {
    exe="${1%.scm}"
    csc "$1"
    "$exe" $2 2>&1
    rm "$exe"
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
    n="${i%.tt}"

    echo $i \
        && ./ttstar -v "$i" &> "$n.out" \
        \
        && ./ttstar "$i" --dump-scheme "${n}.scm" \
        && scheme "${n}.scm" $(cat "${n}.args" 2>/dev/null) &> "${n}.scm.out" \
        \
        && ./ttstar "$i" --skip-inference --dump-scheme "${n}-unerased.scm" \
        && scheme "${n}-unerased.scm" $(cat "${n}.args" 2>/dev/null) &> "${n}-unerased.scm.out"
done
