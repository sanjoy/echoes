#!/bin/zsh

ghc -Wall -Werror -isrc -O2 --make src/Main.hs -o echoes
