
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/FirstOrderLogic.lean'>Code</a> for this chapter</span>
 # First Order Logic

## Limitations of Propositional Logic

The main thing missing from propositional logic is objects. For example, suppose we wanted reason about statements like:

- Every person who lives in Seattle lives in Washington.
- There exists a person who does not live in Seattle.

These statements would be difficult in propositional logic, although given that there are only a finite number of people in the world we could say things like:

- lives_in_seattle_eric → lives_in_washington_eric
- lives_in_seattle_fred → lives_in_washington_fred
- ...

where we create new propositions for every person and every statement we would like to say about that person. However, what if we wanted to reason about an infinite domain like ℕ and say things like the following?

- every natural number is either odd or even

Since there are an infinite number of natural numbers, we need an infinite number of propositions

- odd_0, even_0, odd_1, even_1, ...

## First Order Logic

First order logic (FOL) enriches propositional logic with the following elements:

- **Objects**: such as numbers, names, people, places, etc.
- **Functions**: that transform objects into other objects -- See next set of notes
- **Predicates**: that relate objects to objects
- **Quantifiers**: ∀ and ∃ that allow us to say:
  - ∀: For all objects ___
  - ∃: There exists an object such that ___
- All the connectives we have encountered so far: ∨, ∧, →, ¬, ...
- **Types**: Traditional FOL does not have types, but we will use them anyway)

For example, in the following proposition built from these elements:
```
∀ x ∃ y , f x > y
```
is read "For all x, there exists a y such that f(x) is greater than y". In this example,
- The objects x and y are presumbly numbers
- The symbol f is a function that maps numbers to numbers
- The symbol > is predicate taking two arguments and return true or false

All of this can be done easily in Lean. 
```lean
variable (f : Nat → Nat)
#check ∀ x : Nat , ∃ y : Nat , f x > y
```
 ### Objects

**Objects** in FOL can come from any agreed upon universe. Since we will be using Lean to work with first order logic, you can just assume that objects are any basic terms: numbers, strings, lists, and so on. FOL does not allow us to quantify over functions and types, only basic objects. 
 #### Example: A Finite Universe of People

For example, suppose we wanted to reason about a finite number of people. In Lean we can enumerate them with a new type: 
```lean
inductive Person where | mary | steve | ed | jolin

open Person

#check ed
```
 #### Example : Natural Numbers, Strings, Booleans, etc

Lean has a number of built inn types we can use, such as numbers, strings, and Booleans.

```lean
#check 1234
#check "uwece"
#check true
```
 ## Predicates

A **predicate** is a `Prop` valued function.

#### Example: A Predicate on People

A predicate on Person is a function from Person into Prop, such as one which might specify whether the person lives in Seattle: 
```lean
def InSeattle (x : Person) : Prop := match x with
  | mary  | ed    => True
  | steve | jolin => False

#check InSeattle

example : InSeattle steve ∨ ¬InSeattle steve :=
  Or.inr (λ h => h)
```
 #### Example: A Predicate on ℕ

Or we might define a predicate inductively on the natural numbers. 
```lean
def is_zero(n : Nat) : Prop := match n with
  | Nat.zero => True
  | Nat.succ _ => False

#check is_zero

example : ¬is_zero 91 :=  -- is_zero 91 → False
  λ h => h

theorem t : is_zero 0 := True.intro

theorem t1 : True := True.intro
```
 ## Predicates with Multiple Arguments

We may define predicates to take any number or arguments, including no arguments at all. 
```lean
-- No argument predicates are just normal propositions
variable (P : Prop)
#check P

-- A one-argument predicate
variable (InWashington : Person → Prop)
#check InWashington steve

-- A two-argument predicate
variable (Age : Person → Nat → Prop)
#check Age jolin 27
```
 ### Relations

A two-argument predicate is called a relation.

Example: We might define a predicate on pairs of people such as 
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
 #### Greater Than is a Relation 
 Relations are usually represented with infix notation, but they are still just predicates. For example, in Lean, the greater-than relation on natural numbers is: 
```lean
#check @GT.gt Nat
#eval GT.gt 2 3
```
 This doesn't look very nice, so Lean defines notation:

  infix:50 " > "  => GT.gt

and we can write: 
```lean
#eval 2 > 3
```
 Similarly, >=, <, <=, != are all relations available in Lean. 
 ## Universal Quantification

In FOL, we use the symbol ∀ to denote universal quantification. You can think of univeral quantifiaction like a potentially infinte AND:
```
∀ x P(x)   ≡    P(x₁) ∧ P(x₂) ∧ P(x₃) ∧ ...
```

Example: Here's how you say "All people who live in Seattle also live in Washington":
```
∀ x : Person , InSeattle(x) → InWashington(x)
```

Example: In Lean, let's say we wanted to prove that every person either lives in Seattle or does not live in Seattle. A proof of this fact has the form of a function that takes an arbtrary person x and returns a proof that that person either lives in Seattle or does not. Thus, we can say: 
```lean
example : ∀ (x : Person) , (InSeattle x) ∨ ¬(InSeattle x) :=
  λ x => match x with
  | steve => Or.inr (λ h => h)
  | mary => sorry
  | ed => sorry
  | jolin => sorry
```
 ∀ is just syntactic sugar for polymorphism. The above FOL statement can be equally well written as: 
```lean
#check (x : Person) → (InSeattle x) ∨ ¬(InSeattle x)
```
 Which highlights why we can just use a lambda to dispatch a forall.

## Forall Introduction and Elimination

The universal quantifer has the introduction rule:
```
                   Γ ⊢ P
  ∀-intro ————————————————————————
               Γ ⊢ ∀ x : α, P
```

Where x is not in the free variables of `Γ`. The rule states that if we can prove `P` in context `Γ` assuming `x` not mentioned elsewhere in `Γ`, then we can prove `∀ x : α, P`.

We also have the elimination rule:
```
             Γ ⊢ ∀ x , P x
  ∃-elim ————————————————————————
                  P t
```

where `t` is any term. This rule states that if we know `P x` holds for every `x`, then it must hold for any particular `t`.

### Proving Statements with ∀

The Curry-Howard Isomorphism works for universal quantification too. We could do as we did with proposotional logic and rewrite the FOL rules as type inference. However, here we just say what it means in Lean (which amounts to the same thing).

- **∀-intro**: To prove `∀ x , P x` we construction a function that takes any `x` and returns proof of `P x`. This is an extension of the λ-abstraction rule.

- **∀-elim**: Given a proof `h` of `∀ x , P x` (which we recall is a λ-abstractionn) and a particular `y` of type `α`, we can prove `P y` by simply applying `h` to `y`. This is an extension of the λ-application rule.

For example, here is a proof that uses both of these rules: 
```lean
variable (α : Type) (P Q : α → Prop)

example : (∀ x : α, P x ∧ Q x) → ∀ y : α, P y :=
  λ h q => (h q).left
```
 ## Exists

The `∃` quantifer is like an OR over a lot of propositions:
```
∃ x , P(x)  ≡   P(x₁) ∨ P(x₂) ∨ ....
```

and it has similar introduction and elimination rules:
```
             Γ ⊢ φ[x:=t]                Γ ⊢ ∃ x , φ     Γ, φ ⊢ ψ
  ∃-intro: ———————————————     ∃-elim: ———————————————————————————
             Γ ⊢ ∃ x, φ                        Γ ⊢ ψ
```

Constructively, the first rule says that if we have a proof of `φ` with `x` some term `t` substituted in for `x`, then we have a proof of `∃ x, φ`.

The second says that if we have a proof of `∃ x, φ` and also a proof of `ψ` assuming `φ`, then we have a proof of ψ.

### Lean's Implementation of Exists

In FOL, ∃ is usally just an abbreviation for as `¬∀¬`. However, from a constructive point of view:

> knowing that it is not the case that every `x` satisfies`¬p` is not the same as having a particular `x` that satisfies p. (Lean manual)

So in Lean, `∃` is defined inductively and constructively: 
```lean
namespace temp

inductive Exists {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x) : Exists p

end temp
```
 All we need to introduce an existentially quantified statement with predicate `P` is an element and a proof that `P` holds for that element.

An example use of the introduction rule is the following. Note the assumption that `α has at least one element q` is necessary.  
```lean
example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  λ hp => Exists.intro q (hp q)
```
 ### Exists Elimination

The ∃-elim rule is defined in Lean as follows: 
```lean
namespace temp

theorem Exists.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : Exists (λ x => P x)) (h₂ : ∀ (a : α), P a → b) : b :=
  match h₁ with
  | intro a h => h₂ a h

end temp
```
 In this rule

  b is an arbitrary proposition
  h₁ is a proof of ∃ x , p x
  h₂ is a proof that ∀ a , p a → b

which allow us to conclude b 
 ### Exists Elimination Example

For example, in 
```lean
example (h₁ : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h₁
  (λ c h => Exists.intro c (And.intro h.right h.left))
```
 ## Example Proofs 
```lean
variable (p: Type → Prop)
variable (r : Prop)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (λ h => Exists.elim h (λ c h => And.intro (Exists.intro c h.left) h.right))
  (λ h => Exists.elim h.left (λ c h1 => Exists.intro c (And.intro h1 h.right)))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (λ h x hp => h (Exists.intro x hp))
  (λ h he => Exists.elim he (λ y hy => h y hy))

example : ∀ (x : Person) , (InSeattle x) ∨ ¬(InSeattle x) :=
  λ x => match x with
    | mary  | ed    => Or.inl trivial
    | steve | jolin => Or.inr (λ h => False.elim h)

example : (∀ x : α, P x ∧ Q x) → ∀ y : α, P y :=
  λ h : ∀ x : α, P x ∧ Q x =>
  λ y : α =>
  (h y).left

example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  λ h => Exists.intro q (h q)

example (h₁ : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  have h₂ := λ w : α =>                                            -- proof of ∀
             λ hpq : P w ∧ Q w  =>                                 -- proof of →
             (Exists.intro w (And.intro hpq.right hpq.left))
  Exists.elim h₁ h₂
```
 ## Exercises

<span></span>
1) Prove the following FOL examples using introduction, elimination, etc using either direct proofs or tactics. Do not use the built in theorems from the standard library that match these, that's too easy. 
```lean
variable (p q : Type → Prop)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  sorry
```
 <span></span> 2) Consider the following definition of the sum of the first n squares. 
```lean
def S (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n*n + S x
```
 Show the following result using induction. 
```lean
example (n : Nat) : 6 * (S n) = (n * (n+1)) * (2*n+1) :=
  sorry
```
 <span></span> 3) Given the definitions of Person, on_right, and next_to: 
```lean
inductive Person where | mary | steve | ed | jolin
open Person

def on_right (p : Person) := match p with
  | mary => steve
  | steve => ed
  | ed => jolin
  | jolin => mary

def next_to (p q : Person) := on_right p = q ∨ on_right q = p
```
 Prove the following examples: 
```lean
example : ∀ p , ∀ q , on_right p = q → next_to p q :=
  sorry

example : ∀ p : Person, ∃ q : Person, next_to p q :=
  sorry

example : ∀ p : Person, ∃ q : Person, ¬next_to p q :=
  sorry
```
 <span></span> 4) Besides ∀ and ∃, there are other quantifiers we can define. For example, the "Exists Exactly One" quantifer allows you to state that there is only one of something. We usually written ∃! as in

```hs
    ∃! x, P x
```

which states there is exactly one `x` such that `P x` is true.

We can define this quantifer inductively, just as we did for Exists: 
```lean
inductive Exists1 {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x ∧ ∀ y : α, p y → x = y) : Exists1 p
```
 However, it is a pain to define the notation E!. So we will just have to write

```hs
    Exists1 (λ x => P x)
```

instead of the above.

a) <span></span> Prove the elimination theorem for Exists1 
```lean
theorem Exists1.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : Exists1 (λ x => P x)) (h₂ : ∀ (a : α), P a → b) : b := sorry
```
 <span></span> b) Prove the following examples: 
```lean
example : ∀ x, Exists1 (λ y : Person => x ≠ y ∧ ¬next_to y x ) :=  by
  sorry

example (α : Type) (P : α → Prop) : Exists1 ( λ x => P x ) → ¬ ∀ x, ¬ P x  := sorry

example : Exists1 (λ x => x=0) := sorry

example : ¬Exists1 (λ x => x ≠ 0) := sorry
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
