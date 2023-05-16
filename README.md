# Lambda Calculus Formalizations

This repository contains formalizations of various lambda calculi. The goal in these formalizations is:
 * Implemented in a theorem prover - current choice is Lean though I have experimented with Agda and Coq.
 * Prove interesting properties about the language, in particular, type safety and strong normalization.
 * Hopefully continue to learn about type theories and gradually increase the scope of my knowledge until I can implement a novel programming language to some degree.

Right now, the plan is to proceed through the [PFPL](http://www.cs.cmu.edu/~rwh/pfpl.html) book and gradually implement the various languages mentioned within. These are the languages I have implemented so far, please click the links for more information on each.

1. [**E**](E/)

2. [**EF**](EF/)

3. [**System T**](T/)

Note that a lot of the code is almost exactly the same between implementations. This is intentional. For the purposes of
actually getting stuff done, it's much faster to just copy-paste rather than trying to abstract out common parts. This
is especially true since all the languages are completely independent from each other.

## TODO

Things I want to try eventually, with my knowledge ranging from non-existent to somewhat knowledgeable.

 * Dependent types

 * Linear types

 * Full compiler:

    + Creating an intermediate representation (IR) that is type safe and mapped to from the typing derivations.
    + Implement optimization passes over the IR.
    + Maybe some simple formalization of the x86 architecture, enough to be able to compile to native code.

  * Implicit computational complexity - be able to formulate space/time complexities of functions

