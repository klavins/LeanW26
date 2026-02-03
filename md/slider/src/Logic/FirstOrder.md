
First Order Logic
===


Limitations of Propositional Logic
===

Propositional logic has no *objects*. Suppose we wanted reason about statements like:

- Every person who lives in Seattle lives in Washington.
- There exists a person who does not live in Seattle.

These statements would be difficult in propositional logic, although
we could say things like:

- `lives_in_seattle_eric → lives_in_washington_eric`
- `lives_in_seattle_fred → lives_in_washington_fred`
- `...`

where we create new propositions for every person and every statement we would
like to say about that person.

What if we wanted to reason about an
infinite domain like ℕ and say things like the following?

- every natural number is either odd or even

Since there are an infinite number of natural numbers, we need an infinite number of propositions

- `odd_0, even_0, odd_1, even_1, ...`

First Order Logic
===

First order logic (FOL) enriches propositional logic with the following elements:

- **Objects**: such as numbers, names, people, places, etc.

- **Functions**: that transform objects into other objects

- **Predicates**: that relate objects to objects

- **Quantifiers**: ∀ and ∃ that allow us to say:
    - ∀: For all objects ___
    - ∃: There exists an object such that ___

- **Connectives**: All the connectives we have encountered so far: ∨, ∧, →, ¬, ...

- **Types**: Traditional FOL does not have types, but we will use them anyway

Examples
===

For example,
```
∀ x ∃ y , f x > y
```
is read "For all `x`, there exists a `y` such that `f(x)` is greater than `y`". In this example,
- The objects `x` and `y` are presumably numbers
- The symbol `f` is a function that maps numbers to numbers
- The symbol `>` is `Prop` values function of two arguments

All of this can be done easily in Lean. 
```lean
variable (f : Nat → Nat)
#check ∀ x : Nat , ∃ y : Nat , f x > y
```

Objects
===

**Objects** in FOL can come from any agreed upon universe.
Since we will be using Lean to work with first order logic,
you can just assume that objects are any basic terms: numbers,
strings, lists, and so on.

In what follows, we'll use a simple type with four values. 
```lean
inductive Person where | mary | steve | ed | jolin

open Person

#check ed                    -- Person
```

Predicates
===

A **predicate** is a `Prop` valued function.

For example, a predicate on `Person` is a function from `Person` into `Prop`.

For example, 
```lean
def InSeattle (x : Person) : Prop := match x with
  | mary  | ed    => True
  | steve | jolin => False

#check InSeattle
```
 Predicates can be used with connectives to make compound propositions. 
```lean
example : InSeattle steve ∨ ¬InSeattle steve :=
  Or.inr id
```

Example: A Predicate on ℕ
===

Or we might define a predicate inductively on the natural numbers. 
```lean
def is_zero (n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ _ => False

#check is_zero

example : ¬is_zero 91 :=              -- is_zero 91 → False
  id                                  -- False → False (definitionally)

example : is_zero 0 :=                -- True (definitionally)
  trivial
```

Predicates with Multiple Arguments
===

We may define predicates to take any number or arguments, including no arguments at all. 
 No-argument predicates are just normal propositions 
```lean
variable (P : Prop)
#check P
```
 A one-argument predicate 
```lean
variable (InWashington : Person → Prop)
#check InWashington steve
```
 A two-argument predicate 
```lean
variable (Age : Person → Nat → Prop)
#check Age jolin 27
```

Relations
===

A two-argument predicate is called a **relation**.

For example, we might define a predicate on pairs of people such as 
```lean
def on_right (p q : Person) : Prop := match p with
  | mary => q = steve
  | steve => q = ed
  | ed => q = jolin
  | jolin => q = mary
```
 We can define other predicates in terms of existing predicates. 
```lean
def next_to (p q : Person) := on_right p q ∨ on_right q p

example : next_to mary steve :=
  Or.inl (Eq.refl steve)
```

Greater Than is a Relation
===

 Relations are often represented with *infix* notation, but they are still just
predicates. For example, in Lean, the greater-than relation on natural numbers is: 
```lean
#check @GT.gt Nat
#eval GT.gt 2 3
```
 This doesn't look very nice, so Lean defines notation:

```lean
infix:50 " > "  => GT.gt
```
and we can write: 
```lean
#eval 2 > 3
```
 Similarly, `>=`, `<`, `<=`, and `!=` are all relations available in Lean. 

Exercise
===

<ex /> Define the relation `on_left` for `Person`.

<ex /> Prove
```lean
example : on_left mary jolin := sorry
```


Universal Quantification
===

In FOL, we use the symbol ∀ to denote universal quantification.
You can think of universal quantification like a potentially infinite AND:
```
∀ x P(x)   ≡    P(x₁) ∧ P(x₂) ∧ P(x₃) ∧ ...
```

Example: Here's how you say "All people who live in Seattle also live in Washington":
```
∀ x : Person , InSeattle x → InWashington x
```

Example
===

In Lean, let's say we wanted to prove that every person either lives in
Seattle or does not live in Seattle.

A proof of this fact has the form of a function that takes an arbitrary person `x`
and returns a proof that that person either lives in Seattle or does not.

Thus, we can say: 
```lean
example : ∀ (x : Person) , (InSeattle x) ∨ ¬(InSeattle x) :=
  fun x =>
  match x with
  | steve => Or.inr id
  | mary => sorry
  | ed => sorry
  | jolin => sorry
```

Classical reasoning is not required `InSeattle` explicitly lists all cases,
providing a constructive proof of each one.


∀ is Syntactic Sugar
===

`∀` is just syntactic sugar for polymorphism. The above FOL statement
can be equally well written as: 
```lean
#check (x : Person) → (InSeattle x) ∨ ¬(InSeattle x)
```
 highlighting why we can just use a `λ` to dispatch a `∀`.

Forall Introduction and Elimination
===

The universal quantifier has the introduction rule:
```none
                   Γ ⊢ P
  ∀-intro ————————————————————————
               Γ ⊢ ∀ x : α, P
```

Where x is not in the free variables of `Γ`. The rule states that if we can prove `P` in context `Γ`
assuming `x` not mentioned elsewhere in `Γ`, then we can prove `∀ x : α, P`.

We also have the elimination rule:
```none
             Γ ⊢ ∀ x , P x
  ∃-elim ————————————————————————
                  P t
```

where `t` is any term. This rule states that if we know `P x` holds for every `x`,
then it must hold for any particular `t`.

Proving Statements with ∀
===

The Curry-Howard Isomorphism works for universal quantification too.
We could prove it as we did with propositional
 logic and rewrite the FOL rules as type inference.

- **∀-intro**: To prove `∀ x , P x` we construction a function that takes
any `x` and returns proof of `P x`.
This is an extension of the λ-abstraction rule.

- **∀-elim**: Given a proof `h` of `∀ x , P x` (which must be a function)
and a particular `y`
of type `α`, we can prove `P y` by simply applying `h` to `y`.
This is an extension of the λ-application rule.

For example, here is a proof that uses both of these rules: 
```lean
variable (α : Type) (P Q : α → Prop)

example : (∀ x, P x ∧ Q x) → ∀ y, P y :=
  fun h y => (h y).left
```

Exercise
===

<ex /> Show the following using a term level proof and without using Lean's library of theorems.


```lean
example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := sorry
```

Existential Quantification
===

The `∃` quantifier is like an OR over a (potentially infinite) set of propositions:
```none
∃ x , P(x)  ≡   P(x₁) ∨ P(x₂) ∨ ....
```

and it has similar introduction and elimination rules:
```none
             Γ ⊢ φ[x:=t]                Γ ⊢ ∃ x, φ[x]     Γ ⊢ ∀ x, φ → ψ
  ∃-intro: ———————————————     ∃-elim: ————————————————————————————————————
             Γ ⊢ ∃ x, φ                            Γ ⊢ ψ
```

Constructively, the first rule says that if we have a proof of `φ` with some
term `t` substituted in for `x`, then we have a proof of `∃ x, φ`.

The second says that if we have a proof of `∃ x, φ` and also a proof of `ψ`
assuming `φ`, then we have a proof of `ψ`.

Lean's Implementation of Exists
===

In FOL, ∃ is usually just an abbreviation for as `¬∀¬`. However, from a constructive point of view:

> knowing that it is not the case that every `x` satisfies`¬p` is not the same
as having a particular `x` that satisfies p. (Lean manual)

So in Lean, `∃` is defined inductively and constructively:

```lean
inductive Exists {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x) : Exists p
```

which you should recognize as a `Prop`-values version of `Sigma`.

 Lean defines the shorthand 
```lean
#check ∃ x, P x
```
 for 
```lean
#check Exists (fun x => P x)
```

Using Exists-intro
===

All we need to introduce an existentially quantified statement with predicate `P`
is an element and a proof that `P` holds for that element.

An example use of the introduction rule is the following.
The assumption that `α has at least one element q` is necessary.  
```lean
example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  fun hp => Exists.intro q (hp q)
```
 Or more concisely, 
```lean
example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  fun hp => ⟨ q, hp q ⟩
```

Exercise
===

<ex /> Prove the following


```lean
example : ∃ x, on_right mary x := sorry
example : ∃ x, ¬on_right mary x := sorry
```

<ex /> Using your definition of `PreDyadic` show:
```lean
example : ∀ x , ∃ y, y = neg x := sorry
```



Exists Elimination
===

The ∃-elim rule is defined in Lean as follows:

```lean
theorem Exists.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : ∃ x, P x) (h₂ : ∀ (a : α), P a → b) : b :=
  match h₁ with
  | Exists.intro a h => h₂ a h
```

end temp

In this rule

- `b` is an arbitrary proposition
- `h₁` is a proof of `∃ x , p x`
- `h₂` is a proof that `∀ a , p a → b`

which allow us to conclude `b`. 

Exists Elimination Example
===

For example, 
```lean
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  sorry                                      -- ⊢  ∀ (a : α), P a ∧ Q a → ∃ x, Q x ∧ P x
```
 
```lean
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  (fun c ⟨ hq, hp ⟩ => sorry)                -- ⊢ ∃ x, Q x ∧ P x
```
 
```lean
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  (fun c ⟨ hq, hp ⟩ => ⟨ c, sorry ⟩)         -- ⊢  c ∧ P c
```
 
```lean
example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  (fun c ⟨ hq, hp ⟩ => ⟨ c, ⟨ hp, hq ⟩ ⟩ )
```

Example Proofs
===

```lean
variable (p : Type → Prop) (r : Prop)
```
 You can use pattern matching and brackets to do proof-golfing 
```lean
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := ⟨
    (fun ⟨ c, ⟨ hc, hr ⟩ ⟩ => ⟨ ⟨ c, hc ⟩, hr ⟩ ),
    (fun ⟨ ⟨ c, hc ⟩, hr ⟩ => ⟨ c, ⟨ hc, hr ⟩ ⟩ ) ⟩
```
 But sometimes it is easier to read if you do not: 
```lean
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h x hp => h (Exists.intro x hp))
  (fun h he => Exists.elim he (fun y hy => h y hy))
```
 Here is an example using `Person`: 
```lean
example : ∀ (x : Person) , (InSeattle x) ∨ ¬(InSeattle x) :=
  fun x => match x with
    | mary  | ed    => Or.inl trivial
    | steve | jolin => Or.inr (fun h => False.elim h)
```

Intermediate Results
===

The keyword `have` is like `let`, except for `Prop`. You can use it to
define intermediate results.

```lean
example (h₁ : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=

  have h₂ : ∀ w, P w ∧ Q w → ∃ x, Q x ∧ P x :=
            fun w =>
            fun hpq : P w ∧ Q w  =>
            ⟨ w, ⟨ hpq.right, hpq.left ⟩ ⟩

  Exists.elim h₁ h₂
```

Exercises
===

<ex /> Prove the following FOL examples using introduction, elimination, etc.
using term level proofs (and withouth using library theorems).


```lean
--hide
variable (p q : Type → Prop)
variable (r : Prop)
--unhide

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=  sorry
```

<ex /> Given the definitions of `Person`, `on_right`, and `next_to`:

Prove the following examples: 
```lean
example : ∀ p q , on_right p q → next_to p q := sorry
example : ∀ p : Person, ∃ q : Person, next_to p q := sorry
example : ∀ p : Person, ∃ q : Person, ¬next_to p q := sorry
```

Exists Exactly One
===

Besides `∀` and `∃`, there are other quantifiers we can define.
For example, the "Exists Exactly One" quantifier allows you to state
that there is only one of something. We usually written `∃!` as in

```hs
    ∃! x, P x
```

which states there is exactly one `x` such that `P x` is true.

We can define this quantifier inductively, just as we did for `Exists`: 
```lean
inductive Exists1 {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x ∧ ∀ y : α, p y → x = y) : Exists1 p
```
 However, it is a pain to define the notation `E!`. So we will just have to write

```lean
Exists1 (fun x => P x)
```

instead of the above.

Exercises
===

<ex /> Prove the elimination theorem for `Exists1`


```lean
theorem Exists1.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : Exists1 (fun x => P x)) (h₂ : ∀ (a : α), P a → b) : b := sorry
```

<ex /> Prove the following examples:

```lean
example : ∀ x, Exists1 (fun y : Person => x ≠ y ∧ ¬next_to y x ) := sorry
example (α : Type) (P : α → Prop) : Exists1 ( fun x => P x ) → ¬ ∀ x, ¬ P x  := sorry
example : Exists1 (fun x => x=0) := sorry
example : ¬Exists1 (fun x => x ≠ 0) := sorry

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

