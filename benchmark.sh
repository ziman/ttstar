#!/usr/bin/env bash

PROGRAMS="palindrome"
INPUT_SIZES="$(seq 1 3 64)"

export TIMEFORMAT="%4U"

echo '"program","erasure","input.size","runtime"'
for prog in ${PROGRAMS}; do
    for input_size in ${INPUT_SIZES}; do
        p="examples/$prog"
        unerased_runtime="$(
            (time csi -qs "$p"-unerased.scm ${input_size} > /dev/null) 2>&1
        )"
        erased_runtime="$(
            (time csi -qs "$p".scm ${input_size} > /dev/null) 2>&1
        )"
        echo "\"${prog}\",unerased,${input_size},${unerased_runtime}"
        echo "\"${prog}\",erased,${input_size},${erased_runtime}"
    done
done
