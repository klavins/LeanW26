
Equality
===


Objects, Functions and Equality
===

We extend the first order logic to deal with functions of objects in our universe.
A critical components is a notion of **equality** between objects.

Astonishingly, Lean's equality is not a built in type, but is defined in the standard library.
Once we have equality, we can start working with statements
about functions and their relationships in earnest.

Equality is Defined Inductively
===

To lean how equality works, let's define our own version of it.

```lean
universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl a : MyEq a a

#check MyEq 1 2

example : MyEq 1 1 :=
  MyEq.refl 1
```
 We can define notation 
```lean
infix:50 " ~ "  => MyEq

#check 1 ~ 1
```

Refl is Powerful
===

Terms that are beta-reducible to each other are considered definitionally equal.
You can show many of equalities automatically 
```lean
example : 1 ~ 1 :=
  MyEq.refl 1
```
 The `apply` tactic figures out what the argument to `refl` should be. 
```lean
example : 2 ~ (1+1) := by
  apply MyEq.refl

example : 9 ~ (3*(2+1)) := by
  apply MyEq.refl
```

These proofs do not use rules of arithmetic like associativity.
The use proof by computation (reducibility). So
```lean
| refl a : MyEq a a
```
works for any two definitionally equivalent forms of `a`.



Substitution
===

Substitution is the second most critical property of the equality.
It allows us to conclude, for example, that if `x = y` and `p x` then `p y`. 
```lean
theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
                   (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁ with
  | refl => exact h₂
```
 The cases tactic compiles a term that uses the recursor for `MyEq`.

**Example:** Here is an example where we substitute `y` for `x`
to prove equality between two propositions. 
```lean
example {x y : Nat} : x ~ y → (x > 2 ↔ y > 2) := by
  intro h
  apply MyEq.subst h       -- goal becomes x > 2 ↔ x > 2
  exact ⟨ id, id ⟩
```

Symmetry and Transitivity
===
You can use substitution to show the standard properties we know and love about equality. 
```lean
theorem MyEq.sym {α : Sort u} {a b : α} : a ~ b → b ~ a := by
  intro h
  apply MyEq.subst h
  exact MyEq.refl a

theorem MyEq.trans {α : Sort u} {a b c : α} : a ~ b → b ~ c → a ~ c := by
  intro hab hbc
  exact MyEq.subst hbc hab
```
 Here is an example showing the use of both of these theorems at once. 
```lean
example {x y z : Nat} : y ~ x → z ~ y → x ~ z := by
  intro h1 h2
  apply MyEq.trans (MyEq.sym h1) (MyEq.sym h2)
```

Congruence
===

Congruence is critical for equation solving.

```lean
theorem MyEq.congr_arg {α : Sort u} {a b : α} {f : α → α} : a ~ b → f a ~ f b := by
  intro hab
  apply MyEq.subst hab
  exact MyEq.refl (f a)
```
 For example, 
```lean
example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 :=
  fun h => MyEq.congr_arg (f := fun w => 2*w + 1) h
```
 Or, with tactics 
```lean
example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 := by
  intro h
  apply MyEq.congr_arg (f := fun w => 2*w + 1)    -- goal becomes x ~ y
  exact h
```

Lean's Equality
===

Lean's equality relation is called `Eq` and its notation is `=`,
as we have been using. Lean also defines `rfl` to be `Eq.refl _` 
```lean
#print rfl
example : 9 = 3*(2+1) := Eq.refl 9
example : 9 = 3*(2+1) := rfl
```
 Lean provides a long list of theorems about equality, such as 
```lean
#check Eq.symm            -- a = b → b = a
#check Eq.subst           -- a = b → motive a → motive b
#check Eq.substr          -- b = a → p a → p b
#check Eq.trans           -- a = b → b = c → a = c
#check Eq.to_iff          -- a = b → (a ↔ b) when a and b are Prop
#check Eq.mp              -- α = β → α → β
#check Eq.mpr             -- α = β → β → α
#check congrArg           -- (f : α → β), a₁ = a₂ → f a₁ = f a₂
#check congrFun           -- f = g → ∀ (a : α), f a = g a
#check congr              -- (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂
```

Exercises
===

<ex /> Prove the `to_iff` theorem for `MyEq`. Hint, study the proof for `MyEq.subst`.


```lean
theorem MyEq.to_iff (a b : Prop) : a ~ b → (a ↔ b) := sorry
```

The Triangle Macro
===

`h ▸ e` is a macro built on top of `Eq.rec` and `Eq.symm` definitions.

Given `h : a = b` and `e : p a`, the term `h ▸ e` has type `p b`.

`h ▸ e` is like a "type casting" operation where you change the type of `e` by using `h`.

For example:


```lean
example (α : Type) (a b : α) (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b :=
  h₁ ▸ h₂
```
 A nice example is how `Eq.symm` is proved: 
```lean
example (a b : Type) (h : a = b) : b = a := h ▸ rfl
```
 Or `Eq.trans`: 
```lean
theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
  h₂ ▸ h₁
```

Rewriting
===

 `rw[h]`: Rewrites the current goal using the equality h. 
```lean
theorem t1 (a b : Nat) : a = b → a + 1 = b + 1 := by
  intro hab
  rw[hab]
```
 The `rw` tactic is doing a searching for pattern matches and then using
the basic theorems about equality. 
```lean
#print t1      -- theorem LeanW26.t1 : ∀ (a b : ℕ), a = b → a + 1 = b + 1 :=
               -- fun a b hab ↦ Eq.mpr (id (congrArg (fun _a ↦ _a + 1 = b + 1)
               -- hab)) (Eq.refl (b + 1))
```

More Rewriting
===

 To use an equality backwards, use ← (written \left)
```lean
theorem t2 (a b c : Nat) : a = b ∧ a = c → b + 1 = c + 1 := by
  intro ⟨ h1, h2 ⟩
  rw[←h1, ←h2]
```
 You can also rewrite assumptions using `at`. 
```lean
example (a b c : Nat) : a = b → a = c → b + 1 = c + 1 := by
  intro h1 h2
  rw[h1] at h2
  rw[h2]
```
 Rewrite variants include 
```lean
#help tactic rewrite          -- rewrite without rfl at the end
#help tactic nth_rewrite      -- rewrite a specific sub-term
```

The Simplifier
===

 The simplifier uses equations and lemmas to simplify expressions 
```lean
theorem t3 (a b : Nat) : a = b → a + 1 = b + 1 := by
  simp

#print t3
```
 Sometimes you have to tell the simplifer what equations to use. 
```lean
theorem t4 (a b c d e : Nat)
 (h1 : a = b)
 (h2 : b = c + 1)
 (h3 : c = d)
 (h4 : e = 1 + d)
 : a = e := by
   simp only[h1,h2,h3,h4,Nat.add_comm]

#check Nat.add_comm       -- Try Loogle "Nat" for more
```

The `linarith` Tactic
===

The `linarith` tactic attempts to solve linear equalities and
inequalities and works on `ℕ`, `ℤ`, `ℚ`, `ℝ` and related types.

On `ℕ` and `ℤ` it is incomplete, but on `ℚ` and `ℝ` it is complete.


```lean
example (a b c d e : Nat)
 (h1 : a = b)
 (h2 : b = c + 1)
 (h3 : c = d)
 (h4 : e = 1 + d)
 : a = e := by linarith

example (x y z : ℚ) (h1 : 2*x - y + 3*z = 9)
                    (h2 : x - 3*y - 2*z = 0)
                    (h3 : 3*x + 2*y -z = -1)
 : x = 1 ∧ y = -1 ∧ z = 2 := by
 apply And.intro
 . linarith
 . apply And.intro
   . linarith
   . linarith
```
 ### Example : Induction on Nat

As an example the brings many of these ideas together, consider
the sum of the first `n` natural numbers, which is `n(n+1)/2`.

```lean
def S (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n + S x

example : ∀ n, 2 * S n = n*(n+1) := by
  intro n
  induction n with
  | zero => simp[S]
  | succ k ih =>
    simp[S]
    linarith -- uses ih (check with clear ih before linarith)
```

Exercise
===

<ex /> Try finding a use for `▸` to prove:


```lean
example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z := sorry
```

<ex /> Show the following using the `induction` tactic:


```lean
example (n : Nat) : 6 * (S n) = n * (n+1) * (2*n+1) :=  sorry
```

Inequality
===

Every inductive type comes with a theorem called `noConfusion`
that states that different constructors give different objects. 
```lean
inductive Person where | mary | steve | ed | jolin
open Person

example : mary ≠ steve := by
  intro h
  exact noConfusion h

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

example : MyNat.zero ≠ MyNat.zero.succ := by
  intro h
  exact MyNat.noConfusion h
```

Reasoning using noConfusion
===

Continuing the above example, suppose we want to specify who is on who's right side. 
```lean
def on_right (p : Person) := match p with
  | mary => steve
  | steve => ed
  | ed => jolin
  | jolin => mary

def next_to (p q : Person) := on_right p = q ∨ on_right q = p

example : ¬next_to mary ed := by
  intro h
  cases h with
  | inl hme => exact noConfusion hme
  | inr hem => exact noConfusion hem
```

Trivial
===

The `trivial` tactic (not to be confused with the `trivial` theorem,
sometimes figures out when to apply `noConfusion` 
```lean
theorem t10 : ed ≠ steve := by
  intro h
  trivial

#print t10       -- fun h ↦ False.elim (noConfusion_of_Nat Person.ctorIdx h)
```

Exercises
===

<ex /> For `PreDyadic`, show
```lean
example (x : PreDyadic) : zero ≠ add_one x

example : ¬zero.add_one = zero.add_one.add_one.half := sorry
```
using `noConfusion`.

<ex /> Show
```lean
example (x y : PreDyadic) : add_one x = add_one y ↔ x = y := sorry
```



Equality for Structure Types
===

Two terms of a structure type are equal if the values of their fields
are equal.

For example, given


```lean
structure Point (α : Type u) where
  x : α
  y : α
```
 We can show 
```lean
theorem Point.ext {α : Type} (p q : Point α) (hx : p.x = q.x) (hy : p.y = q.y)
  : p = q := by
  cases p; cases q;
  cases hx; cases hy;
  rfl
```
 Then we can do, for example, 
```lean
example (x y : Nat) : Point.mk (x+y) (x+y) = Point.mk (y+x) (y+x) := by
  apply Point.ext
  · exact add_comm x y
  · exact add_comm x y
```

Defining Extensionality Automatically
===

If we add the @[ext] tag to a definition, we can automatically
define extensionality and register it to be used with the `ext` tactic.

```lean
@[ext]
structure Komplex where
  re : ℝ
  im : ℝ

example (x y : ℝ) : Komplex.mk (x+y) (x+y) = Komplex.mk (y+x) (y+x) := by
  ext
  · exact add_comm x y
  · exact add_comm x y
```

Function Extensionality
===

Two functions are considered equal if they assign the same value to every
argument. The theorem that allows us to prove that is 
```lean
#check funext -- (∀ (x : α), f x = g x) → f = g
```
 Here is an example: 
```lean
def f (n : ℕ) := n + 1
def g (n : ℕ) := 1 + n

example : f = g := by
  funext x
  unfold f g              -- not needed, but makes it easy to see the goal
  rw[add_comm]
```

<div class='fn'>In some languages, function extensionality is an axiom.
In Lean, it follows from the properties of quotients (which we will get in to
later). This approach was possibly first described in
<a href="https://ncatlab.org/nlab/files/HofmannExtensionalIntensionalTypeTheory.pdf">Extensional concepts in intensional type theory</a> by Martin Hoffman. </div>


Exercises
===

<ex /> For `PreDyadic` show
```lean
example : double ∘ half = id := sorry
```


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

