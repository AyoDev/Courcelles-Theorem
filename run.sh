#!/bin/bash
./tw-exact -s 4321 < $1 > temp.td
./Main $1 temp.td > temp.mona
line=( $(head -n 1 temp.td) )
width=${line[0]}
echo $width
python codegen.py ${line[3]} "${@:2}" > test.mona ;mona test.mona
