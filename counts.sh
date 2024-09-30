#!/bin/bash

echo "Printing statistics for file $1"

# Count LoC of file
echo "LoC:"
dafny /rprint:- /noAutoReq /noVerify /env:0 /printMode:NoIncludes $1 | wc -l

# Count occurneces of function/method/lemma
fCount=`dafny /rprint:- /noAutoReq /noVerify /env:0 /printMode:NoIncludes $1 | grep -o -i function | wc -l`
pCount=`dafny /rprint:- /noAutoReq /noVerify /env:0 /printMode:NoIncludes $1 | grep -o -i predicate | wc -l`
mCount=`dafny /rprint:- /noAutoReq /noVerify /env:0 /printMode:NoIncludes $1 | grep -o -i method | wc -l`
lCount=`dafny /rprint:- /noAutoReq /noVerify /env:0 /printMode:NoIncludes $1 | grep -o -i lemma | wc -l`

let "fpCount = $fCount + pCount"

echo "${fCount}/${pCount}"
echo "${fpCount}/${mCount}/${lCount}"
