

Fork of `robotone` to be found in https://github.com/mg262/research
The work of Mohan Ganesalingham and Tim Gowers in their paper "A Fully Automatic Theorem Prover with Human-Style Output".

As the original article states: This article is distributed under the terms of the Creative Commons Attribution 4.0 International License (http://creativecommons.org/licenses/by/4.0/), which permits unrestricted use, distribution, and reproduction in any medium, provided you give appropriate credit to the original author(s) and the source, provide a link to the Creative Commons license, and indicate if changes were made.

# Build and run

Install `haskell-stack`, which is a reproducible build system for haskell. Also make sure you have a latex engine installed.

``` bash
# in our project directory
git clone https://github.com/EdAyers/Robotone.git
cd Robotone
stack build
```

Create a directory into which the build files will go:

```
mkdir build
```

Then run `run.sh build`, which effectively does this;

``` bash
# generate a TeX file
stack exec robotone-exe > build/robotone.tex
# for just the human-readable output
cd build
xelatex "\input{robotone.tex}"
# for full explanation of reasoning process
xelatex "\def\showsteps{1} \input{robotone.tex}"
```

Note, the TeX file requires the libertine.sty fonts, available in Debial from `texlive-fonts-extra`.
