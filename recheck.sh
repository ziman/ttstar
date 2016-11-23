#!/bin/bash

scheme_racket() {
    racket -r $1.scm > $1.scm.out
}

scheme_csi() {
    csi -qb "$1".scm > $1.scm.out
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
