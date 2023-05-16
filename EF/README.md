# **EF**

This is a Lean 4 implementation of the **EF** lambda calculus variant described in chapter 8 of [PFPL](http://www.cs.cmu.edu/~rwh/pfpl.html). Well, it differs slightly. **EF** in the book extends **E** but I didn't want to have to carry over all the extra expressions like `plus` and `times`, so I removed a few of them that weren't important to the topic of the chapter. This does however make the language essentially useless computationally speaking as you have abstractions and applications, but there's nothing you can really compute with them.

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

I moved onto this implementation after having completed **E** and it was mostly smooth sailing. I pretty much copied that implementation and adjusted it for the new expressions.

### Normalization

The one place I did get stuck on for a few days was on the proof for weak normalization. Like **E**, I followed http://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/kripke-steps.pdf, though this time I had to follow it more closely with the introduction of higher types (i.e. the arrow type). My proof isn't exactly like theirs but it's close, the only difference being that I changed the definition of `HereditarilyNormalizing` for arrow types to require that the expression be weakly normalizing. The paper doesn't require this as part of the definition and they end up having to prove it separately. I think the approach I took is simpler as it doesn't require the definition to allow for weakened contexts.

The updated proof of hereditarily normalizing to account for arrow types wasn't too bad, I figured it out pretty fast. What was problematic was that the proof showing that the identity substitution preserves hereditarily normalizing terms was no longer trivial. What this proof essentially requires is a direct proof that variable terms are hereditarily normalizing. Without arrow types this is trivial, but with them it's not (well, at least for me). The paper handles this by proving a conjecture that repeated applications on a variable is hereditarily normalizing. Even stating the conjecture in Lean was a bit of a pain and required quite a bit of machinery. The most problematic portion came when I started having to do rewrites on the indexes of indexed types (e.g., `Any` and `Expr`) that there not definitionally equal.

I got stuck on this part for a while. I knew I had the proof essentially done, but there were a lot of technicalities around `Eq.mp`/`Eq.mpr`/etc. showing up in my terms that prevented unification from happening. I eventually went to the Lean Zulip and asked for some advice. They pointed out some examples of a pattern where you define `cast` operators for your types that allow you to cast an indexed type to another indexed type provided you gave a proof their indices were propositionally equal. You then prove lemmas about the cast operators which allow for simplification in certain cases. Updating my proof to use these cast operators allowed the resulting expression to be simplified from the cast lemmas and it eventually was accepted.

## Questions

There are a couple of things I feel like I don't have full clarity on.

* One thing is that in order to implement the interpreter, I had to require that the user uses type ascriptions on the input argument for every lambda. I understand why this is needed in some cases, e.g., the type of the term `(ʎ x . x)` cannot be inferred because it can really an arrow type `τ -> τ` for any `τ`. But I'm pretty sure there are situations in which it can be inferred though maybe not in this language. My two open thoughts here are:
    
    1. How would I update the type checker to infer the input type whenever it wasn't ambiguous. My typechecker right now is just implemented in a simple bidirectional way, but I feel like this would require some kind of constraint solver? I'm not sure.

    2. I'm pretty sure I shouldn't need to require type ascriptions for terms like `(ʎ x . x)` if the language supported some degree of polymorphism.

* I was a bit surprised to find that open terms could be values. PFPL includes abstractions are values, even if they included open variables. And looking at other formalizations like PLFA and SF, they do the same. I guess it only became important when I tried to copy over how I handled evaluation from **E**. In **E**, I could easily formalize an algorithm that would essentially strip the context from a value, so if `e : Γ ⊢ τ` and `Value e`, then it could be mapped to `e' : ⊢ τ` such that `Value e'`. In **EF**, this didn't work anymore because abstractions can be open variables. So the way I went about evaluating arbitary open terms was to first recursively substitute all open variables in the given term, then evaluate it as a closed term. I'm not sure if this would create problems in more complex type theories. I tried adjusting the proof of `Progress` to work on open terms, but I got a bit confused on how to best formalize it because variable substitutions aren't covered by the transition relation.
