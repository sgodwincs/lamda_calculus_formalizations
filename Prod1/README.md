# **Prod1**

This is a Lean 4 implementation of the nullary and binary product (no specific name given in book) lambda calculus variant described in chapter 10 of [PFPL](http://www.cs.cmu.edu/~rwh/pfpl.html).

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

In the book, **Prod1** doesn't have abstractions or applications, but I kept them in because it seems rather boring without them and I wanted to see how the arrow and product types would interact.

### Normalization

As expected, the only place that gave any trouble was normalization. I had to once again generalize the proof that all neutral terms are hereditarily normalizing. Before, the only higher type eliminator was application, but now projections were added. I ended up having to consider any sequence of eliminators, including `application`, `proj₁`, and `proj₂`. It didn't take too much work, and now I have a framework setup for adding additional eliminators. In particular, I'm hoping it will allow me to easily do the normalization proof for both finite product times and binary sum types which are the next things I plan to do.

### Neutral Terms

One thing I noticed during the implementation was that I'm not allowing all the reductions possible to occur. For example, I only allow projections to reduce if it's on a value pair. Theoretically I could allow it to reduce even if the pair was neutral, but it turned out I would require additional constraints on the projection neutral forms to ensure that the underlying expression was not a pair. Otherwise, it would be a neutral term that reduced which obviously isn't right. I decided to just stick with requiring it to be values (and I noticed I did something similar for the recursor in **System T**). Maybe in the next variant I'll allow eliminator to always apply, even on neutral forms.

## Next

Up next will be implementing a variant with finite product types. I expect this could give me a significant amount of trouble. I may have to deal with permutations of list, sub-lists, etc. and it could get messy fast.
