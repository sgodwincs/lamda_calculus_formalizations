# **TyGem**

This is a Lean 4 implementation of the (type) generic programming (no specific name given in book) lambda calculus variant described in chapter 14 of [PFPL](http://www.cs.cmu.edu/~rwh/pfpl.html).

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

Been working on this one on and off, honestly the idea of a generic extension map was a bit confusing to me at first and only after trying to implement it did I understand what it was really doing. This language combines both sum and product types as needed by the polynomial type operators. Most of the work was trying to formalize the transitions for the generic extension expression, which gave me particular trouble with some Lean stuff. My first attempt had type operator substitution as a recursive definition, but Lean didn't like this because even though the function was injective, I wasn't sure how to show that to Lean during elimination. Proving it separately wouldn't have helped since it was a part of the normalization flow from what I understand.

Other than that, proving strong normalization was the most tricky portion per usual.

### Normalization

I had to separate out all the individual proofs of hereditary normalization for each expression type into separate proofs because this was the first time where I needed to reuse them for a different proof. The generic extension transition ends up using pretty much every other expression and thus would require normalization proofs for those. Doing this for the product types was trivial, but it took a bit of thought on how to organize it when binders started being introduced (e.g. for binary case and abstraction). However, once I figured it out for one, it was trivial to figure out how to do the next. Once again though, I'm reminded of how incredibly useful it is to have implemented the substitution rewrite system using Lean's `simp` tactic. So many times I have some incredibly complicated expression involving substitutions, but it turns out just calling `simp` reduces it greatly or removes the substitutions entirely!

## Next

Next is chapter 15, covering inductive and coinductive types. I have a feeling this could take me a long while, to not only understand the formalisms but implementing it seems like it could be quite challenging.