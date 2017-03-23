#!/usr/bin/env bash

PROGRAMS="palindrome"
INPUT_SIZES="$(seq 1 1 64)"
NSAMPLES="10"

export TIMEFORMAT="%4U"

echo '"program","erasure","input.size","sample.no","runtime"'
for prog in ${PROGRAMS}; do
    for input_size in ${INPUT_SIZES}; do
        p="examples/$prog"
        for sample_no in $(seq ${NSAMPLES}); do
            unerased_runtime="$(
                (time csi -qs "$p"-unerased.scm ${input_size} > /dev/null) 2>&1
            )"
            erased_runtime="$(
                (time csi -qs "$p".scm ${input_size} > /dev/null) 2>&1
            )"
            echo "\"${prog}\",unerased,${input_size},${sample_no},${unerased_runtime}"
            echo "\"${prog}\",erased,${input_size},${sample_no},${erased_runtime}"
        done
    done
done
