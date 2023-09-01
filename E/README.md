# **E**

This is a Lean 4 implementation of the **E** lambda calculus variant described in chapters 4-7 of [PFPL](http://www.cs.cmu.edu/~rwh/pfpl.html).

## Notable design decisions include:
 * Reduction:
    + Call-by-value
    + Weakly normalizing, i.e., reduction leads to weak head normal forms 
 * 3-layered expression representation definition:
    + A surface-level syntax representation that is mapped directly from the parser. Importantly, variables are represented as strings here.
    + An intrinsically scoped representation where variables are now De Bruijn indices. The surface-level representation can be converted to this via the scope checker.
    + An intrinsically typed representation where only well-typed expressions are allowed by construction. The scoped representation can be converted to this via the type checker.
 * Substitution is treated in a way that allows for decidable, terminating equality checks between expressions containing only substitution operators. This is based off of the σ-algebra as described in Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution by Schafer, Tebbi, and Smolka (ITP 2015). The primary purpose of which is to allow Lean to automatically handle this via `simp` and it was quite useful during the proof of normalization.
 * Pretty much every type introduced is in the sort `Type` rather than `Prop`. I originally started with putting stuff in `Prop`, but as I got closer to a working interpreter, this obviously stopped being realistic. For the most part, this didn't cause problems, but there are a few instances where it did. One particular spot is that I wanted to implement the `WellFounded` typeclass for my types, but I couldn't because my reduction relation `Transition` is in `Type` and not `Prop`.

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

This was the first fully implemented and proven language I've done in general. It was also my first time doing something non-trivial in Lean and it was quite difficult for me. It took quite a while for me to get comfortable with the tactics available and there is surely more room to grow (I haven't taken a look at how Mathlib4 could have helped).

For my reference, these were the parts of the implementation that gave me the most trouble:
 * I originally took the approach of using an extrinsically typed representation. This seemed more intuitive to me, and I got quite far with this. Where it started to cause significant problems was in certain proofs of equality between terms where `HEq`s started popping up. I didn't know how to proceed, so I decided to switch to an intrinsically typed representation. This actually just resulted in large amounts of code being deleted!
 * Likewise, I was originally using my own `Vector` implementation instead of a `List` for the definition of `Context`. For like 99% of the implementation, this never caused a problem. The one spot where it started introducing problems was when I started implementing the σ-algebra, specifically the implementation of `extᵣ`. This caused the same problems as mentioned above (introduction of `HEq`s). Someone on the Lean Zulip suggested a pattern that is used in Mathlib to deal with these kinds of equalities between types. I made some progress by doing so (not completely), but decided to just go with using a `List` instead. I will likely continue to use `List` for future implementations until I reach a point where a `Vector` would provide significant benefit.
 * Implementing the σ-algebra. This actually was the hardest part (at least in terms of how long it took me) of the entire implementation and it came down to just one proof in particular. I was actually expecting this to be rather easy because I was able to follow most of what is mentioned in the corresponding [PLFA chapter](https://plfa.github.io/Substitution/). However, the noticeable difference is that their implementation is only for the UTLC and the introduction of different types in mine caused various issues. The file with the implementation in this repo has more details on the particular proof I had trouble with.
 * Proving weak normalization. So this language is actually almost completely trivial to prove weak normalization for, except for the presence of the `let` expression. I took the approach of using logical relations, in particular I followed the proof as described in http://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/kripke-steps.pdf. It turns out I didn't need to go as far as they did to complete the proof, but it was very helpful in getting me to the endpoint. I expect that as I start working in more complex lambda calculi, their approach will be instrumental.
 * Proving strong normalization. I actually had thought that proving strong normalization would be trivial. This is because I had already proven weak normalization and determinism which together imply strong normalization. But I just couldn't figure out how to make that step, especially when taking into account the constructive definition of well-foundedness (i.e. accessibility). I got quite stuck because in my mind, I needed termination of reduction in order to proving termination which confused me a lot. Interestingly, I tried using ChatGPT to help a bit. I was a bit wary of using ChatGPT because I wasn't completely confident I could discern whether it was telling the truth, and in general it wasn't very helpful. It suggested certain approaches that didn't seem realistic to me. Eventually though, it suggested that I prove strong normalization by first showing a well-foundedness relation on the size of terms which I could do using determinism and weak normalization. In hindsight, this seems completely obvious, but it was a big step in helping me get a better understanding of well-foundedness and termination in Lean.
 * A *lot* of problems in Lean dealing with not being able to perform a rewrite that I thought I would be able to. A huge thanks to everyone on the Lean Zulip for helping me through various problems, it has increased my toolset significantly and hopefully these problems will happen less over time.
 * Other problems in Lean around the usage of mutually recursive inductive types or functions. Sometimes Lean would complain about not being able to prove termination, but I was always able to figure out how to convince it (without even using `termination_by`).
