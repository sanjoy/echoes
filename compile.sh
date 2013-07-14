#!/usr/bin/zsh

if [[ -z $1 ]]; then
    echo "Usage: $0 input-file [ output-file ]"
    echo "  output-file defaults to `basename input-file`.out"
    exit 1
fi

if [[ -z $2 ]]; then
    OUTPUT="`basename $1`.out"
else
    OUTPUT=$2
fi

~/src/echoes/dist/build/echoes/echoes --input=${1} --output ${OUTPUT}.S
gcc -g3 ${OUTPUT}.S src/Runtime/runtime-x86.S src/Runtime/runtime.c -o ${OUTPUT}
rm -r ${OUTPUT}.S

