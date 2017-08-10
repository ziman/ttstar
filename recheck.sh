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
    csc "$1" \
        -O5 \
        -unsafe \
        -strict-types \
        -optimize-leaf-routines \
        -specialize \
        -inline \
        -block \
        -fixnum-arithmetic \
        -no-argc-checks \
        -no-bound-checks \
        -no-procedure-checks \
        -clustering \
        -lfa2
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

mkdir -p examples/outputs
for i in examples/*.tt; do
    n_src="${i%.tt}"
    n="${n_src/examples/examples\/outputs}"

    rm -f "${n}"{,-unerased}{,-NF}.*
    echo $i

    ./ttstar -v --solver indexed "$i" &> "${n}.out" \
        || continue  # skip if it doesn't typecheck

    ./ttstar "$i" \
        --solver indexed \
        --opt-identity \
        --dump-pretty "${n}-erased.tt" \
        --dump-scheme "${n}.scm" \
        --dump-nf     "${n}-NF.tt" \
        --dump-nf-scheme "${n}-NF.scm" \
        && scheme "${n}.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}.scm.out" \
        && scheme "${n}-NF.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}-NF.scm.out"

    ./ttstar "$i" --skip-inference \
        --solver indexed \
        --dump-pretty "${n}-unerased.tt" \
        --dump-scheme "${n}-unerased.scm" \
        --dump-nf     "${n}-unerased-NF.tt" \
        --dump-nf-scheme "${n}-unerased-NF.scm" \
        && scheme "${n}-unerased.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}-unerased.scm.out" \
        && scheme "${n}-unerased-NF.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}-unerased-NF.scm.out"
done
