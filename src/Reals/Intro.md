
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Reals/Intro.lean'>Code</a> for this chapter</span>
 # Real Numbers

Having built ℕ inductively, then building ℤ from ℕ and ℚ from ℕ and ℤ, we now turn to the real numbers ℝ. The key distinction between ℚ and ℝ is that ℝ has the least upper bound property: every non-empty set of reals that is bounded from above has a least upper bound. The rationals ℚ do not have this property. For example, the set
```hs
{ q ∈ ℚ | q² < 2 }
```
has no least upper bound in ℚ, although in ℝ the least upper bound is `√2` (for a Lean proof that the square root of 2 is no rational, see [Chapter 5](https://leanprover-community.github.io/mathematics_in_lean/C05_Elementary_Number_Theory.html#irrational-roots) of _MIL_.)

The usual way to construct ℝ, and the one taken by Mathlib, is to define `Cauchy Sequences` over `ℚ` that converge to irrational values. For example, the sequence
```
  4/1
  4/1 - 4/3
  4/1 - 4/3 + 4/5
  4/1 - 4/3 + 4/5 - 4/7
  4/1 - 4/3 + 4/5 - 4/7 + 4/9
```
Converges to `π`.

In this chapter, mainly as an exercise in formalization, we instead construct ℝ from _Dedekind Cuts_ in which every real number is equated to the set of rational numbers less than it. We roughly follow the decription of this approach presented in Rudin's book _Principles of Mathematical Analysis_ (which also, by the way, describes the Cauchy Sequence approach.)

## Axioms of the Reals

To show that a set R is equivalent to the real numbers, we must define the following relations and operations:

- Ordering relations: <, ≤, > and ≥
- Addition and subtraction: +, -
- Multiplication: *
- Division: /

and then prove the following:

- R is totally ordered: ∀ x y ∈ R, x < y ∨ y < x ∨ x=y
- R is a field
  - Addition properties
    - Addition is commutative: x+y=y+x
    - Addition is associative: x+(y+z) = (x+y)+z
    - There is an additive identity 0 and x+0 = 0+x = x.
    - Each element x has an additive inverse -x such that x+(-x) = 0.
  - Multiplication properties
    - Multiplication is commutative: x*y=y*x
    - Multiplication is associative: x*(y*z) = (x*y)*z
    - There is a multiplicative identity 1 and x*1 = 1*x = x.
    - Each element x has a multiplicative inverse x⁻¹ such that x*x⁻¹ = x⁻¹*x = 1.
 - R has the least upper bound property

Mathlib defines classes for all of these properties. Thus, as we prove them in Lean, we will register intances of these classes (and several others) so that our construction works with all of the theorems and tactics that Mathlib provides for notation, ordering, groups, rings, and fields.

<span style='background: yellow'>TODO: List the relevant Mathlib classes or insert a tree diagram of them.</span>

## References

A nice description of the Cauchy Completion: https://mathweb.ucsd.edu/~tkemp/140A/Construction.of.R.pdf

Rudin, W.: Principles of Mathematical Analysis. Third Edition. International Series in Pure and Applied Mathematics. McGraw-Hill Book Co., New York – Aukland – Dusseldorf, 1976.

A real analysis book in which ℝ is constructed from decimal expansions of the form f : ℕ → ℤ with f(0) being the integer part and f(n) ∈ {0, ..., 9} for n ≥ 1. [Davidson and Donsig](https://docs.ufpr.br/%7Ehigidio/Ensino/Seminario/Davidson-Donsig-2010-Real%20Analysis%20and%20Aplications.pdf)  

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
