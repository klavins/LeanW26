import Mathlib

namespace LeanW26


/-
Curry-Howard Isomorphism
===
-/

/-

Curry-Howard Isomorphism Intuition
===

Consider the types:
```
A → A
(C → A) → C → A
```

The first is the type of a function on `A`. The second is the type of a
function that takes a function on `C → A`.

Wwe can read these as propositional formulas stating
```
A implies A
(C implies A) implies C implies A
```

The **Curry-Howard Isomorphism** emerges from the observation that the λ expressions
having the above types look like the proofs that the above implications are tautologies!

With this observation, the statement x : A reads "x is a proof of A".
```
λ x : A => x
```

is a method that takes a proof of `A` and returns a proof of `A`, proving the implication `A → A`.




Types ≡ Propositions
===

To state the CHI exacly, we will restrict ourselves to showing that Propositional Logic with only implication (→) is isomorphic to the simply typed λ-calculus. We will need one definition.

**Def:** Given a context Γ = { x₁: φ₁, x₂ : φ₂, ..., xₙ : φₙ }, the _range_ of Γ, denoted |Γ|, is { φ₁, φ₂, ..., φₙ }.

**Theorem:** If Γ ⊢ M : φ then |Γ| ⊢ φ.

**Proof Sketch:** We convert any type derivation tree into a propositional proof by replacing VAR with AX, ABST with →-Intro, and APPL with →-Elim. This is done by induction on the proof tree. Here we just show an example which should be easily generalized. The type proof tree in the previous section can be re-written be removing all "x : "
```
    ————————————————————— AX       ———————————————————— AX
     C → A, C  ⊢  C → A               C → A, C  ⊢  C
  ——————————————————————————————————————————————————————————— →Elim
                      C → A, C   ⊢  A
                    ——————————————————— →-Intro
                      C → A  ⊢  C → A
                   —————————————————————— →-Intro
                    ⊢  (C → A) → C → A
```

Curry-Howard: Propositions → Types
===

The opposite direction of the CHI is more technical. We have to show how to produce a λ-calculus term M from a proof of `φ` so that `M : φ`. For example, suppose we started with the propositional proof tree in the previous section. How would we produce the type derivation from it? Here we will outline how this is done in general.

First we need a way to produce a type context from a propositional context. Suppose that
```
Γ = { φ₁, φ₂, ..., φₙ }
```

and define
```
Δ = { x₁ : φ₁, x₂ : φ₂, ..., xₙ : φₙ }
```

where the `xᵢ` are introduced as new type variables. The object `Δ` is a function of `Γ` of course, but we just don't write it this way.

**Theorem:** If `Γ ⊢ φ` then there exists a λ-calculus term `M` such that `∆ ⊢ M:φ`.

The proof of this theorem uses induction on the proof tree that shows `Γ ⊢ φ`. Since there are three rules (AX, →Intro, and →-Elim), we have three cases, which we handle one by one.

*Case:* The proof ends with `Γ,φ ⊢ φ` by the VAR rule

*Subcase 1*: If `φ ∈ Γ` then there is some type variable `x` such that `x : φ ∈ Δ`. By the VAR rule we can conclude
```
Δ  ⊢  x : φ
```

*Subcase 2*: If `φ ∉ Γ` then we introduce a new variable `x` such that `x : φ`. Once again by the VAR rule
```
Δ, x : φ  ⊢  x : φ
```

(Why do we need two sub-cases? It's because of how we defined `Δ` on the previous as related to `Γ` and not to `Γ ∪ { x : φ }`).

*Case:* The proof ends with →Elim

Suppose the proof that `Γ ⊢ φ` ends with
```
    Γ ⊢ ρ → φ      Γ ⊢ ρ
  ——————————————————————————
           Γ ⊢ φ
```
We need to find a λ-term that has type `φ`. Here the premises of the above rule instance allow us to assume the induction hypothesis that there exists `M` and `N` such that
```
Δ ⊢ M : ρ → φ
Δ ⊢ N : ρ
```
By the ABST rule, we can conclude
```
Δ ⊢ M N : φ
```

*Case:*: The proof ends with →Intro

Suppose the proposition `φ` has the form the `ρ → ψ` and the proof `Γ ⊢ ρ → ψ` ends with
```
     Γ, ρ ⊢ ψ
  ——————————————
    Γ ⊢ ρ → ψ
```

Subcase 1: `ψ ∈ Γ`. By the induction hypothesis, there is a term `M` such that `Δ ⊢ M : ψ`. Introduce a variable `x` (not used in `Δ`) such that `x : ρ`. Then we can conclude
```
Δ, x : ρ  ⊢  M : ψ
```

and by the ABST rule
```
Δ ⊢ λ x : ρ => M : ρ →  ψ
```

Subcase 2: `ψ ∉ Γ`. Then by the induction hypothesis, there is a term `M` such that
```
Δ, x : ρ ⊢ M : ψ
```

from which we may also conclude
```
Δ ⊢ λ x : ρ => M : ρ →  ψ
```
-/


/-
Propositions, Theorems, and Proofs in Lean
===

The Curry-Howard approach is exactly how proofs of theorems are done in Lean. We show that the proposition to be proved is inhabited. In the examples below, we use the type Prop, from Lean's standard library.

We will start by declaring two variables of type Prop. We use curly braces here instead of parentheses for reasons we will explain later. -/

variable { A C : Prop }

/- To prove a proposition like A → A, we define the identity function from A into A, showing the proposition considered as a type is occupied. We have called the bound variable in the lambda expression _proof_, but you could call the bound variable anything you like. -/

def my_theorem : A → A :=
  λ proof : A => proof

/- Lean provides the keyword _theorem_ for definitions intended to be results, which is like def but does requires the type of the theorem being defined to be Prop. The theorem keyword also gives Lean and the user an indication of the intended use of the definition. -/

theorem my_lean_theorem : A → A :=
  λ proof : A => proof

/-
Applying Theorems to Prove Other Theorems
===

As another example, we prove the other proposition we encountered above. Here we call the bound variables pca for "proof of c → a" and pc for "proof of c".  -/

theorem another_theorem : (C → A) → C → A :=
  λ pca : C → A =>
  λ pc : C =>
  pca pc

/- Or even better, we can use our first theorem to prove the second theorem: -/

theorem another_theorem_v2 : (C → A) → C → A :=
  λ h : C → A => my_lean_theorem h

/-
More Examples
===
-/

theorem t1 : A → C → A :=
  λ pa : A =>
  λ pc : C =>                                -- Notice that pc is not used
  pa

theorem t2 : A → C → A :=
  λ pa pc  => pa                             -- We can use λ with two arguments

theorem t3 : A → C → A :=
  λ pa _ => pa                               -- We can tell Lean we know pc is not used

example : A → C → A :=                       -- We can state and prove an unnamed theorem
  λ pa _ => pa                               -- using the `example` keyword

/-
Negation
===

There are, of course, only so many theorems we can state using only implication. In the next chapter we will show how the λ-calculus can be extended to include `∧`, `∨`, and `False`. To give a sense of how this looks, here is an example using `¬p`, which as you will recall is the same as `p → False`. -/

variable (p q: Prop)

example : p → ¬p → q :=
  λ pa pna => absurd pa pna

example : (p → q) → (¬q → ¬p) :=
  fun hpq nq hp => absurd (hpq hp) nq

/- Here, absurd is a theorem from the Lean standard library that we will discuss when we get to Lean's `inductive type` system.

Variable Declarations
===

If we had used
```hs
variable (A C : Prop)
```

above, then my_lean_theorem would have (A : Prop) as a non-implicit argument, so it would have to be applied as
```hs
my_lean_theorem hca h
```

which is ugly.

The way Lean uses variables is by putting them silently into all definitions and theorems that use them. So my_theorem internally looks like:
```hs
theorem my_lean_theorem (A : Prop) : A → A :=
  λ proof : A => proof
```

On the other hand, if we use curly braces in the variable declaration, as we did in the previous examples, then we get
```hs
theorem my_lean_theorem {A : Prop} : A → A :=
  λ proof : A => proof
```
so that the type of A is an implicit argument to my_lean_theorem. -/

/-
References
===

Morten Heine Sørensen, Pawel Urzyczyn
"Lectures on the Curry-Howard Isomorphism"
Elsevier. 1st Edition, Volume 149 - July 4, 2006.
  - Chapter 4 describes Intuitionistic Propositional Logic

-/



--hide
end LeanW26
--unhide
