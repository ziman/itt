#!/usr/bin/env bash

stack build --fast

for fname_tt in examples/*.tt; do
    fname_out="${fname_tt%.tt}.out"

    echo "processing ${fname_tt}"
    stack exec itt "$fname_tt" > "$fname_out"
done
