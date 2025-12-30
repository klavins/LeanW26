
Introduction
===

What is this Course About?
===

The representation and manipulation of mathematical knowledge symbolically
  - Foundations of Mathematics
  - Automated reasoning
  - The L∃∀N proof assistant

Specific Topics
  - Type theory
  - The Curry-Howard Isomorphism
  - Representation of mathematical objects
  - Meta-level programming about mathematics
  - Applications to AI and ML

Why Now?
===

- The theory underlying proof assistants is mature and active
    - Basis Calculus of Inductive Constructions (CIC)
    - Advanced: [HOTT](https://homotopytypetheory.org/)
- The software and tooling has improved considerably
    - Implementation tradeoffs in CIC optimized
    - Improved modularity
    - IDE support
    - Multiple options: L∃∀N, Rocq, Agda, ...
- Major projects like [Mathlib](https://github.com/leanprover-community/mathlib4), [SciLean](https://github.com/lecopivo/SciLean), [FLT](https://lean-lang.org/use-cases/flt/), [LTE](https://leanprover-community.github.io/blog/posts/lte-final/), ...
    - Adoption by well known mathematicians like [Terrence Tao](https://github.com/teorth/analysis)
- LLMs
    - Make advanced programming tractable for mortals
    - Can auto-formalize mathematical text into L∃∀N

Proof Assistants and Math
===

[The Liquid Tensor Experiment](https://leanprover-community.github.io/blog/posts/lte-final/)
- Peter Scholze worried there could be some subtle gap in his result on Condensed Sets with Dustin Clausen.
- He posed a challenge: Encode it in Lean.
- A group of volunteers led by Johan Commelin produced a Lean version of the main theorem in six months.

> I find it absolutely insane that interactive proof assistants are now at the level that, within a very reasonable time span, they can formally verify difficult original research.
>
> — Peter Scholze

<div class='fn'>Nature 595, 18-19 (2021), doi: https://doi.org/10.1038/d41586-021-01627-2</div>

Formalized Mathematics
===

The Mathlib project and others have formalized even more.

<div><small><pre>
> ls Mathlib
Algebra                 Data                    LinearAlgebra           RingTheory
AlgebraicGeometry       Deprecated              Logic                   SetTheory
AlgebraicTopology       Dynamics                Mathport                Std
Analysis                FieldTheory             MeasureTheory           Tactic
CategoryTheory          Geometry                ModelTheory             Tactic.lean
Combinatorics           GroupTheory             NumberTheory            Testing
Computability           InformationTheory       Order                   Topology
Condensed               Init.lean               Probability             Util
Control                 Lean                    RepresentationTheory

> find Mathlib -name '*.lean' -print0 | xargs -0 wc -l | tail -1
  615506 total
</pre>
</small></div>

<div class='fn'>https://github.com/leanprover-community/mathlib4</div>


Math and AI
===

LLMs are great at generating text, images, and designs.
But they are not often grounded in reality.

However if you put Lean and an LLM into a feedback loop, you get a sort of
left-brain / right-brain system, which is increasingly powerful.

Math and AI Companies
===

- [DeepMind / AlphaProof](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/)
- [Aristotle] (https://aristotle.harmonic.fun/)
- [Axiom](https://axiommath.ai/)
- [Math, Inc](https://www.math.inc/)
- [DeepSeek Prover](https://prover-v2.com/)
- And many more ...


Course Details
===

Topics
- Type Theory
- Logic, Number, Sets, Relations, ...
- Domain Specific Languages
- Meta-programming
- Interfacing L∃∀N to other languages

Homework
- Each slide deck has exercises interspersed and at the end
- Exercises are due as a standalone lean file in canvas 1 week after the deck is completed in class

Project
- Formalize an interesting (to you) area of mathematics in Lean


Use of AI
===

GPT, Gemini, DeepSeek etc. are good at generating / fixing Lean code. Aristotle is quite good.

Most of the exercises in this course can be solved by an AI with some back and forth.

Formalizing a new area of mathematics is harder because it involved *defining* the framework,
not just proving theorems. It is hard to prove anything is a poor formalization.

Just because an AI answered your question, doesn't mean you understand the answer

If you want to build new tools, even AIs, based on Lean (or similar tools),
you need to know those tools



Resources
===
- Canvas
- These slides : [https://faculty.washington.edu/klavins/LeanW26/dist](https://faculty.washington.edu/klavins/LeanW26/dist)
- Slides on github: [https://github.com/klavins/LeanW26](https://github.com/klavins/LeanW26)


```lean
--hide
end LeanW26
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

