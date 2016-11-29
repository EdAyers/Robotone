#!/usr/bin/bash
wd=$(dirname "$0")
cat src/*.hs | grep -v -E '^[[:space:]]*($|--( |$)|//)' | wc -l