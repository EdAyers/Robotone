#!/bin/bash
wd=$(dirname "$0")
xelatex=$(which xelatex)

stack exec robotone-exe > "$wd/build/robotone.tex"
echo "TeX"
pushd "$wd/build"
"$xelatex" "\input{robotone.tex}" -jobname=robotoneshort -quiet
"$xelatex" "\def\showsteps{1} \input{robotone.tex}" -jobname=robotone -quiet
popd