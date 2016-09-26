#!/bin/bash

for i in examples/*.tt; do
    n=${i%.tt}
    echo $i
    ./ttstar $i > $n.out 2>&1 \
        && racket -r $n.scm > $n.scm.out
done
