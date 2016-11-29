#!/usr/bin/bash
wd=$(dirname "$0")
echo
pushd src > 0
for f in *.hs
do  
    paste <(cat $f | grep -v -E '^[[:space:]]*($|--( |$)|//)' | wc -l) <(echo ${f%src.*}) 
done
echo
cat *.hs | grep -v -E '^[[:space:]]*($|--( |$)|//)' | wc -l
popd > 0
echo