#!/usr/bin/bash
wd=$(dirname "$0")
xelatex=$(which xelatex)

pushd "$wd/src"
runghc Main.hs > "../build/robotone.tex"
popd
echo "TeX"
pushd "$wd/build"
"$xelatex" robotone.tex --quiet
popd
open "$wd/build/robotone.pdf"