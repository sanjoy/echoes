#!/bin/zsh

find . -name '*hs' | xargs hlint --color
