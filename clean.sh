#!/bin/zsh

find . -name '*.o' | xargs rm -f
find . -name '*.hi' | xargs rm -f
rm -f echoes
