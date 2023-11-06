# **Sum1**

This is a Lean 4 implementation of the nullary and binary sum (no specific name given in book) lambda calculus variant described in chapter 11 of [PFPL](http://www.cs.cmu.edu/~rwh/pfpl.html).

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

Well, it's been a while since I've pushed any new languages to this repo. Honestly, I was stuck on trying to do **Prod2**
and implement record types, turns out it's quite technically difficult to do so in Lean (at least for me). I spent a
couple of months on it, and it's almost done (statics defined, dynamics like half-way done), but I wanted to get something
out and sum types seemed easy enough.

### Normalization

I wasn't sure how to define what it means for an expression of a sum type to be hereditarily normalizing. Turns out you
can't quite do it like you would with projections and applications. I had the mindset that you always just make it so
the eliminator of the higher-type is hereditarily normalizing, like:

```lean
HereditarilyNormalizing (Expr.proj₁ e) × HereditarilyNormalizing (Expr.proj₂ e)
```

But you can't really do that for sum types because just doing `HereditarilyNormalizing (Expr.binary_case e eₗ eᵣ)` would
cause the definition to no longer be well-founded since the resulting type is an arbitary one, and I can only inductively
use `τₗ` and `τᵣ`. So I made it so that two functions must be provided, one that requires the caller to provide proof that
the normal form of the expression being matched on is of the form `inl`, and if so, I would return that the inner expression
is hereditarily normalizing, likewise for `inr`. This turned out to be a good approach and was pretty easy to move forward
with.

### Neutral Terms

Proving that all neutral terms were hereditarily normalizing was also a bit different than what I did for projections.
For projections, I ended up creating a kind of "framework" that would make it easy to add additional eliminators into
the proof, but as it was for the proof above, I had to approach it different for sum types. Turns out, all of the eliminator
stuff isn't really required for them exactly because of the way hereditary normalization is defined for sum types.

## Next

I do want to get back to trying to finish finite product types and eventually move to finite sum types, but I'm not sure
they're worth the time theoretically speaking. They aren't really complicated in theory, they just require a lot of
technical work, and Lean honestly does not make it easy as it just straight up doesn't allow certain definitions you'd
want to be able to do. It also requires a lot of manual proofs of termination whenever proving anything about records
which just isn't fun to do.

For now, I'll probably move forward with chapter 14, which is generic programming. I'm expecting it will be a lot of fun
and probably quite challenging for me!
