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
    chicken-csi -qs "$1" $2 2>&1
}

# Chicken Scheme, compiler
scheme_csc() {
    exe="${1%.scm}"
    chicken-csc "$1" \
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

#cabal install -j1 \
#    || die "could not install"
stack install \
    || die "could not install"

mkdir -p examples/outputs
for i in examples/*.tt; do
    n_src="${i%.tt}"
    n="${n_src/examples/examples\/outputs}"

    mkdir -p "${n}"
    find "${n}" -type f | xargs rm
    echo $i

    ttstar -v "$i" &> "${n}/ttstar.out" \
        || continue  # skip if it doesn't typecheck

    ttstar "$i" \
        --opt-identity \
        --dump-pretty "${n}/erased.tt" \
        --dump-ir     "${n}/erased.ir" \
        --dump-scheme "${n}/erased.scm" \
        --dump-scheme-ir "${n}/erased-IR.scm" \
        --dump-nf     "${n}/erased-NF.tt" \
        --dump-nf-scheme "${n}/erased-NF.scm" \
        && scheme "${n}/erased.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}/erased.scm.out" \
		&& scheme "${n}/erased-NF.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}/erased-NF.scm.out" \
        && scheme "${n}/erased-IR.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}/erased-IR.scm.out"

    ttstar "$i" --skip-inference \
        --dump-pretty "${n}/unerased.tt" \
        --dump-ir     "${n}/unerased.ir" \
        --dump-scheme "${n}/unerased.scm" \
        --dump-scheme-ir "${n}/unerased-IR.scm" \
        --dump-nf     "${n}/unerased-NF.tt" \
        --dump-nf-scheme "${n}/unerased-NF.scm" \
        && scheme "${n}/unerased.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}/unerased.scm.out" \
		&& scheme "${n}/unerased-NF.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}/unerased-NF.scm.out" \
        && scheme "${n}/unerased-IR.scm" $(cat "${n_src}.args" 2>/dev/null) &> "${n}/unerased-IR.scm.out"
done
