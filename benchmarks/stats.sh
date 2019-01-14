#!/bin/bash

programs="$(ls ../examples/ |  grep '.tt$' | cut -d. -f1)"

echo 'program,loc,bytes,evars,annotations,annotations_used'
for p in $programs; do
    fname=../examples/${p}.tt
    loc=$(wc -l < $fname)
    bytes=$(wc -c < $fname)
    evars=$(ttstar $fname --dump-stats /dev/stdout 2>/dev/null | jq .evars)
    annotations=$(ttstar $fname --dump-stats /dev/stdout 2>/dev/null | jq .annotations)
    annotations_used=$(ttstar $fname --dump-stats /dev/stdout 2>/dev/null | jq .annotations_used)
    echo $p,$loc,$bytes,${evars:-NA},${annotations:-NA},${annotations_used:-NA}
done
