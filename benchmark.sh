#!/usr/bin/env bash

PROGRAMS="palindrome"
INPUT_SIZES="$(seq 1 7 128)"

export TIMEFORMAT="%4U"

echo '"program","input.size","runtime.unerased","runtime.erased"'
for prog in ${PROGRAMS}; do
    for input_size in ${INPUT_SIZES}; do
        p="examples/$prog"
        unerased_runtime="$(
            (time csi -qs "$p"-unerased.scm ${input_size} > /dev/null) 2>&1
        )"
        erased_runtime="$(
            (time csi -qs "$p".scm ${input_size} > /dev/null) 2>&1
        )"
        echo "\"${prog}\",${input_size},${unerased_runtime},${erased_runtime}"
    done
done
