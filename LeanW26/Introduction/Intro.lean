--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.

import Mathlib

namespace LeanW26

/-
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
  - Applications

Why Now?
===

- The theory underlying proof assistants is mature and active
    - Basis: Calculus of Inductive Constructions (CIC)
    - Advanced: [HOTT](https://homotopytypetheory.org/)
- The software and tooling has improved considerably
    - Implementation tradeoffs in CIC optimized
    - Improved modularity
    - IDE support
    - Multiple options: L∃∀N, Rocq, Agda, ...
- Major projects like [Mathlib](https://github.com/leanprover-community/mathlib4), [SciLean](https://github.com/lecopivo/SciLean), [FLT](https://lean-lang.org/use-cases/flt/), [LTE](https://leanprover-community.github.io/blog/posts/lte-final/), ...
    - Adoption by well known mathematicians like [Terrence Tao](https://github.com/teorth/analysis)
    - Potentially a major change in publishing
- LLMs
    - make advanced programming tractable for mortals
    - can auto-formalize mathematical text into L∃∀N


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

Seems like a lot, but _Web of Knowledge_ lists a total of 1,342,406 mathematics papers since 1900.

<div class='fn'>
https://github.com/leanprover-community/mathlib4<br>
https://strathmaths.wordpress.com/2013/04/17/how-much-mathematics-is-there
</div>



Math and AI
===

LLMs
- Great at generating text, images, and designs.
- Not grounded in reality or logic.

<img src='img/brain.jpg' class='img-up-right' width=40%></img>

Integration
- However if you put Lean and an LLM into a feedback<br>
loop, you get a sort of left-brain / right-brain system, <br>
which is increasingly powerful.

As a learning tool
- The combination of LLMs and Lean, even without integration, will make
advanced mathematics more accessible than ever.
- Use wisely : [AI in Papers](https://ai-math.zulipchat.com/#narrow/channel/539992-Web-public-channel---AI-Math/topic/Best.20practices.20for.20incorporating.20AI.20etc.2E.20in.20papers/near/546518354), [AI Generated Papers](https://categorytheory.zulipchat.com/#narrow/channel/229111-community.3A-general/topic/AI-generated.20papers/near/546399334)

AI Companies
- [DeepMind / AlphaProof](https://deepmind.google/blog/ai-solves-imo-problems-at-silver-medal-level/),
[Aristotle] (https://aristotle.harmonic.fun/),
[Axiom](https://axiommath.ai/),
[Math, Inc](https://www.math.inc/),
[DeepSeek Prover](https://prover-v2.com/),
...






Use of AI
===

Current State
- GPT, Gemini, DeepSeek etc. are good at generating / fixing Lean code. Aristotle is quite good.
- Most of the exercises in this course can be solved by an AI with some back and forth.

Limitations
- Formalizing a new area of mathematics is harder because it involved
*defining* the framework,not just proving theorems.
- The choice of representation affects the difficulty of proof.

Learning something
- Just because an AI answered your question, doesn't mean you understand the answer
- If you want to build new tools, including new AIs, based on Lean (or similar tools),
you need to know those tools.

Course Details
===

Topics
- Type theory
- Logic, numbers, sets, relations, ...
- Various mathematical topics
- Domain specific languages
- Meta-programming
- Interfacing L∃∀N to other languages

Homework: 60%
- Each slide deck has exercises interspersed and at the end
- Exercises are due as a standalone Lean file in canvas 1 week after the deck is completed in class

Project: 40%
- Lean centered project that builds on the ideas in this course
   - Formalization, language design, applications, tools, ...
- Rubric TBA

Classroom Etiquette
===

We have undergraduate and graduate students from four different departments!

Some students are new to this area, others have been actively working in it.

Please
- Respect each other
- Ask questions
- Make space for others
- Don't spray beta


Lean W26 Slides
===

What you are seeing is compiled from Lean code using my own custom slide
environment called `Slider`. This tool is not ready for production, so it may
not work on every browser, etc. I use Chrome.

Slides are under construction
- Some topics I am converting from last year's format
- Some I have written all the code for, but not made into slides
- All slides will be marked as _under construction_ until a few days before we cover them

The slides are on the web at:
- [https://faculty.washington.edu/klavins/LeanW26/dist](https://faculty.washington.edu/klavins/LeanW26/dist)

The source code to the slides are at:
- [https://github.com/klavins/LeanW26](https://github.com/klavins/LeanW26)
- Clone this repo and following along in class
- Do `git update` *before* each class meeting

If you find errors, please submit an issue at
- [https://github.com/klavins/LeanW26/issues](https://github.com/klavins/LeanW26/issues)

Resources
===

Course Materials
- Canvas

Supplementary Texts
- Morten Heine Sørensen, Pawel Urzyczyn.
**Lectures on the Curry-Howard Isomorphism**.
Elsevier. 1st Edition, Volume 149 - July 4, 2006.
- **Homotopy Type Theory: Univalent Foundations of Mathematics**.
The Univalent Foundations Program Institute for Advanced Study.
[https://homotopytypetheory.org/book/](https://homotopytypetheory.org/book/).
- Steve Awodey, **Category Theory**, Oxford University Press. 2nd Edition. 2010.

Lean
- <a href="https://lean-lang.org/theorem_proving_in_lean4/" target="other">
  Theorem Proving in Lean
  </a>
- <a href="https://lean-lang.org/functional_programming_in_lean/" target="other">
  Lean Programming Book
  </a>
- <a href="https://leanprover-community.github.io/lean4-metaprogramming-book/" target="other">
  Lean Metaprogramming
  </a>
- <a href="https://leanprover-community.github.io/mathematics_in_lean" target="other">
  Mathematics in Lean
  </a>
- <a href="https://loogle.lean-lang.org/" target="other">
 Loogle
 </a> — Google for Lean
- <a href="https://leanprover.zulipchat.com/" target="other">
  Zulip Chat
  </a> — Discussion groups

-/

/-
Acknowledgements
===

I would like to acknowledge the students who took my special topics course offered the
Winter of 2025 at the University of Washington. We all learned Lean together. At first,
I was a few weeks ahead, and by the end of the course I was a few weeks behind.
 Much of the material here was developed in response to their questions and ideas.

-/


--hide
end LeanW26
--unhide
