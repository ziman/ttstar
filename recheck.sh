#!/bin/bash

for i in examples/*.tt; do
	echo $i
	./ttstar $i > ${i%.tt}.out
done
