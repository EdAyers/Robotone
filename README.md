

Fork of `robotone` to be found in https://github.com/mg262/research
The work of Mohan Ganesalingham and Tim Gowers in their paper "A Fully Automatic Theorem Prover with Human-Style Output".

As the original article states: This article is distributed under the terms of the Creative Commons Attribution 4.0 International License (http://creativecommons.org/licenses/by/4.0/), which permits unrestricted use, distribution, and reproduction in any medium, provided you give appropriate credit to the original author(s) and the source, provide a link to the Creative Commons license, and indicate if changes were made.

Original `README.txt`
-------------


General note
------------

As described in the accompanying paper, the prover relies heavily on data stored in its _library_.  This library needs to be tailored to the problem(s) being solved. It is not possible to build a general, problem-independent library because the prover will use "more advanced" results to prove simpler ones -- for example, using the fact that a polynomial is differentiable to prove that it is continuous. As such, before trying the prover on fresh problems you will need to update the library. Roughly speaking, the library needs to contain domain-specific results and operations that would be obvious to an undergraduate who could be given the problem as an exercise, without containing "more advanced" facts.  

Compilation and Execution
-------------------------

This software should be compiled with ghc 7.8.3 and Cabal 1.18.0.5 using v. 0.6.0.2 of the logict package. You will also need a TeX distribution to compile the generated proofs; the software was tested with MikTeX 2.9.

After the source code has been compiled, run run.sh to generate and compile the TeX output; this will generate PDFs in the build/ subdirectory.  robotoneshort.pdf contains the actual proofs 

Changelog
---------

1.1

Added TestData2 (problems supplied by a referee). 
forwardsLibraryReasoning no longer creates new terms.
matchTargetWithHypothesis no longer displays debug text in writeup.

1.0

Initial release.
