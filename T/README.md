# **System T**

This is a Lean 4 implementation of the **System T** lambda calculus variant described in chapter 9 of [PFPL](http://www.cs.cmu.edu/~rwh/pfpl.html).

## Notable design decisions include:
 * Reduction:
    + Call-by-value
    + Weakly normalizing, i.e., reduction leads to weak head normal forms 
 * 3-layered expression representation definition:
    + A surface-level syntax representation that is mapped directly from the parser. Importantly, variables are represented as strings here.
    + An intrinsically scoped representation where variables are now De Bruijn indices. The surface-level representation can be converted to this via the scope checker.
    + An intrinsically typed representation where only well-typed expressions are allowed by construction. The scoped representation can be converted to this via the type checker.
 * Substitution is treated in a way that allows for decidable, terminating equality checks between expressions containing only substitution operators. This is based off of the σ-algebra as described in Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution by Schafer, Tebbi, and Smolka (ITP 2015). The primary purpose of which is to allow Lean to automatically handle this via `simp`.

## Notable proofs include:
 * Type safety
    + Preservation (not explicitly proved since an intrinsically typed approach is taken)
    + Progress
 * Weak and Strong normalization (i.e. termination) on all well-typed open terms
 * Confluence
 * Determinism
 * Soundness, completeness, and decidability of both the scope and type checkers
 * No potentially unsound features are used (e.g., `axiom`, `sorry`, `partial`) except for `partial` for the parser

## Structure

 * 3-layered expression representation as mentioned above.
 * Language can be broken down into two parts: statics and dynamics as described in PLFA.
 * The path from a string to an evaluation result is as follows:
    + String is parsed.
    + Expression is scope checked.
    + Expression is type checked.
    + Expression is evaluated.

## Learnings

**System T** only adds natural numbers along with a recursor on them. Most of the implementation is the same as **EF**.

### Normalization

Once again, the sticking point was proving normalization. I got stuck for a few days trying to determine how to handle the recursor case. In particular, I wasn't sure how the `HereditarilyNormalizing` logical predicate should handle `Ty.nat` types. I was taking a look at exercise 3 of https://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/tait.pdf which asks for the reader to handle natural numbers as in System T. I think as it's described is a bit confusing for me, but after a brief email exchange with Robert Harper directly I got a better understanding of what to do, that is, using the induction principle for natural numbers. However, the way I went about it wasn't by changing the definition `HereditarilyNormalizing` for `Ty.nat` to be something other than just requiring that it's weakly normalizing. I instead directly used the induction principle in the proof of `hereditarily_normalizing`. After some finagling, I had solved the case where the term reduces to a value.

But I still needed to account for when the term evaluates to a neutral term since I'm proving normalization for all open terms. In **EF**, I had already made a direct proof that variables (a subset of neutral terms) are hereditarily normalizing. I decided to try adjusting this proof to handle all neutral terms, and it was a pretty straightforward transition. The only bump in the road so to speak was having to define additional `cast` operations for the `Value`, `Normal` and `Neutral` types which took me a bit because their indices are themselves castable types.
