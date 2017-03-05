#!/bin/bash

KEEP_INTERMEDIATES="no"
GCC_OPT_LEVEL="-O0"

if [[  "$1" == "--keep-intermediates" ]]; then
    KEEP_INTERMEDIATES="yes"
    shift
fi

if [[ "$1" == "--release-mode" ]]; then
    GCC_OPT_LEVEL="-O3"
    shift
fi

if [[ -z $1 ]]; then
    echo "Usage: $0 [ --keep-intermediates ] [ --release-mode ] input-file [ output-file ]"
    echo "  output-file defaults to `basename input-file`.out"
    exit 1
fi

if [[ -z $2 ]]; then
    OUTPUT="`basename $1`.out"
else
    OUTPUT=$2
fi

ROOT=$(dirname $0)

echo "Intermediate output in ${OUTPUT}.S"

$ROOT/dist/build/echoes/echoes --input=${1} --output=${OUTPUT}.S
clang -g3 ${GCC_OPT_LEVEL} ${OUTPUT}.S $ROOT/src/Runtime/runtime.c \
    $ROOT/src/Runtime/runtime-x86.S -Wl,-no_pie -o ${OUTPUT}

if [[ "$KEEP_INTERMEDIATES" == "no" ]]; then
    rm -r ${OUTPUT}.S
fi
