
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
They use proof by computation (reducibility). So
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

Exercises
===

<ex /> Prove the `to_iff` theorem for `MyEq`. Hint, study the proof for `MyEq.subst`.


```lean
theorem MyEq.to_iff (a b : Prop) : a ~ b → (a ↔ b) := sorry
```

<ex /> Try finding a use for `▸` in a proof of:


```lean
example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z := sorry
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
```
 Sometimes you have to tell the simplifer what equations to use. 
```lean
theorem t4 (a b c d e : Nat)
 (h1 : a = b)
 (h2 : b = c + 1)
 (h3 : c = d)
 (h4 : e = 1 + d)
 : a = e := by
    simp[h1,h2,h3,h4,Nat.add_comm]          -- simp[*] also works

#check Nat.add_comm       -- Try Loogle "Nat" for more
```
 `simp` has many variants: `simp?`, `simp at`, `simp_all`, `dsimp`, `simpa`, `field_simp`, ... 

Adding Theorems to the Simplifier
===

Any theorem of the form `x=y` or `p↔q` can be added to the simplifier. To avoid
loops, it is usually best to have the left hand side be more complicated than the
right hand side.

```lean
inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

postfix:95 " ⁻¹ " => toggle
```
 Let's add some basic theorems to the simplifier. 
```lean
@[simp] theorem toggle_up : up⁻¹ = dn := rfl
@[simp] theorem toggle_dn : dn⁻¹ = up := rfl
```

Using Spin's simps
===

 We can use these theorems to prove another theorem, which is also added to
the simplifier. 
```lean
@[simp] theorem toggle_toggle {x} : x⁻¹⁻¹ = x := by
  cases x <;> simp?  -- uses toggle_up, toggle_dn
```
 And then prove yet another theorem. 
```lean
example {x} : x⁻¹⁻¹⁻¹ = x⁻¹ := by simp -- uses toggle_toggle
```

Adding more simps
===

```lean
def op (x y : Spin) : Spin := match x, y with
  | up,dn => dn
  | dn,up => dn
  | _,_ => up

infix:75 " o " => op
```
 And some simplifications: 
```lean
@[simp] theorem op_up_left {x}  : up o x = x := by cases x <;> rfl
@[simp] theorem op_up_right {x} : x o up = x := by cases x <;> rfl
@[simp] theorem op_dn_left {x}  : dn o x = x⁻¹ := by cases x <;> rfl
@[simp] theorem op_dn_right {x} : x o dn = x⁻¹ := by cases x <;> rfl
```
 Using these, we can show: 
```lean
@[simp] theorem toggle_op_left {x y} : (x o y)⁻¹ = x⁻¹ o y := by
  cases x <;> simp   -- case 1 uses op_up_left, toggle_up, op_dn_left
                     -- case w uses op_dn_left, toggle_toggle, toggle_dn, op_up_left
```

Exercise
===

<ex /> Prove the following using `rw` and `simp`. When you do use `simp`,
make a note of which theorems it is calling for each case (using `simp?`).


```lean
-- Don't @[simp] this one!
theorem assoc {x y z} : x o (y o z) = (x o y) o z := sorry

-- Don't @[simp] this one!
theorem com {x y} : x o y = y o x := sorry

theorem toggle_op_right {x y} : (x o y)⁻¹ = y o x⁻¹ := sorry

theorem inv_cancel_right {x} : x o x⁻¹ = dn := sorry

theorem inv_cancel_left {x} : x⁻¹ o x = dn := sorry
```

The `linarith` Tactic
===

The `linarith` tactic attempts to solve linear equalities and
inequalities and works on `ℕ`, `ℤ`, `ℚ`, `ℝ` and related types.

On `ℕ` and `ℤ` it is incomplete, but on `ℚ` and `ℝ` it is complete.


```lean
example (a b c d e : Nat)
 (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d)
 : a = e := by
 linarith

example (x y z : ℚ) (h1 : 2*x - y + 3*z = 9)
                    (h2 : x - 3*y - 2*z = 0)
                    (h3 : 3*x + 2*y -z = -1)
 : x = 1 ∧ y = -1 ∧ z = 2 := by
 constructor
 · linarith
 · constructor <;> linarith
```

Example : Induction on Nat
===

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
    linarith         -- uses ih (check with clear ih before linarith)
```

Exercise
===

<ex /> Let


```lean
def T (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ x => n*n + T x
```

Show the following using the `induction` tactic:

```lean
example (n : Nat) : 6 * (T n) = n * (n+1) * (2*n+1) :=  sorry
```

Inequality
===

Any two elements of an inductive type constructed differently are not equal. 
```lean
example : up ≠ dn := by
  intro h
  exact Spin.noConfusion h
```

Confused about noConfusion?
===

`Thing.noConfusion` is a `theorem` built from `Thing.noConfusionType`.
We could redefine something like it as follows: 
```lean
def nc_type (P : Prop) (x y : Spin) : Prop :=
  match x, y with
  | up, up => P
  | up, dn => False
  | dn, up => False
  | dn, dn => P

example : nc_type True up up = True  := by rfl
example : nc_type True dn up = False := by rfl

example : up ≠ dn := by
  intro h
  have hAB : nc_type True up dn := by
    rw[←h]                              -- ⊢ nc_type True A A
    trivial
  exact hAB                             -- nc_type True A B is equivalent to False
```

Other Ways to Show Inequality
===

```lean
example : up ≠ dn := by
  intro h
  cases h     -- uses Eq.casesOn, Thing.ctorIdx, and Nat.noConfusion

example : up ≠ dn := by
  intro h
  have : Spin.ctorIdx up = Spin.ctorIdx dn := by rw[h]
  exact Nat.noConfusion this
```
 Or you can use nomatch on `h`. 
```lean
example : up ≠ dn := by
  intro h
  nomatch h
```
 Which is the same as 
```lean
example : up ≠ dn := fun h => match h with .     -- marked as deprecated
```
 All of these methods work with other inductive types like `Nat` and `PreDyadic` as well. 

Reasoning using noConfusion
===

Continuing the above example, suppose we want to specify who is on who's right side. 
```lean
inductive Person where | mary | steve | ed | jolin
open Person

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

The `trivial` tactic (not to be confused with the `trivial` theorem),
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


Example : Shift
===

Suppose we define

```lean
def shift (k x : ℤ) : ℤ := x+k
```
 Then we can show 
```lean
@[simp]
theorem shift_inv_right {k} : shift k ∘ shift (-k) = id := by
  funext x              -- x : ℤ ⊢ (shift k ∘ shift (-k)) x = id x
  simp[shift]

@[simp]
theorem shift_inv_left {k} : shift (-k) ∘ shift k = id := by
  funext x
  simp[shift]
```

Shift is a Bijection
===

Lean's standard library provides a number of theorems about functions in the Function library.

```lean
open Function

#print Bijective                    -- fun {α} {β} f ↦ Injective f ∧ Surjective f
#check bijective_iff_has_inverse    -- Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f
#check leftInverse_iff_comp         -- LeftInverse f g ↔ f ∘ g = id
#check rightInverse_iff_comp        -- RightInverse f g ↔ g ∘ f = id
```
 and more. Use Loogle to look up `Function`.

Using the above, we can show:

```lean
example {k} : Bijective (shift k) := by
  rw[bijective_iff_has_inverse]
  use shift (-k)
  constructor
  · simp[leftInverse_iff_comp]     -- uses shift_inv_left
  · simp[rightInverse_iff_comp]    -- uses shift_inv_right
```

Exercises
===

<ex /> Instead of `shift_inv_left` and `shift_inv_right` as simplifiers, we could have used


```lean
@[simp] theorem shift_zero : shift 0 = id := sorry
@[simp] theorem shift_add {j k} : shift k ∘ shift j = shift (j+k) := sorry
```


Prove these two theorems and show that the proof of `example {k} : Bijective (shift k)` still
goes through, but with the simplifier using `shift_zero` and `shift_add`.

Note: If `shift_inv_left` and `shift_inv_right` are still registered as simps, you can use 
```lean
attribute [-simp] shift_inv_left
attribute [-simp] shift_inv_right
```


<ex /> For `PreDyadic` show
```lean
example : double ∘ half = id := sorry
```





Equiv
===

`Equiv` is a structure defined in [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Defs.html) for showing equivalences between types.
It is defined:

```lean
structure Equiv (α : Sort u_1) (β : Sort u_2) : Sort (max (max 1 u_1) u_2)
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse self.invFun self.toFun
  right_inv : RightInverse self.invFun self.toFun
```

The notation `X ≃ Y` is is used to represent the equivalence and
the library supports the following notation:


```lean
variable (X Y : Type) (x : X) (y : Y)
variable (e : X ≃ Y)

#check e x         -- preferred way to write e.toFun x
#check e.symm y    -- preferred way to write e.invFun y
```
 `Equiv` and its extensiosn are used heavily in Mathlib.  

Example : Natural ≃ Nats
===

Recall we defined an alternative natural number type with:

```lean
mutual
  inductive Ev
  | zero : Ev
  | succ : Od → Ev
  deriving Repr              -- allows Lean to print Ev terms

  inductive Od
  | succ : Ev → Od
  deriving Repr              -- allows Lean to print Od terms
end

def Natural := Ev ⊕ Od

namespace Natural
```

Our goal is to define an equivalnce showing
```lean
Natural ≃ Nat
```


Converting Natural to Nat
===

We first define an `of_nat` function converting a `Nat` to a `Natural`.


```lean
def zero : Natural := .inl Ev.zero

def succ (x : Natural) : Natural := match x with
  | .inl a => .inr (Od.succ a)
  | .inr a => .inl (Ev.succ a)

def of_nat (n : Nat) : Natural := match n with
  | Nat.zero => .zero
  | Nat.succ k => .succ (of_nat k)

#eval Natural.of_nat 3    -- Sum.inr (Od.succ (Ev.succ (Od.succ (Ev.zero))))

instance : Zero Natural := ⟨ .zero ⟩
instance : One Natural := ⟨ .succ .zero ⟩
```

Converting Natural to Nats
===

Next we define a `to_nat` function convering `Natural` to `Nat`.

 
```lean
mutual
  def Ev.to_nat : Ev → Nat
    | .zero => 0
    | .succ k => .succ (Od.to_nat k)
  def Od.to_nat : Od → Nat
    | .succ k => .succ (Ev.to_nat k)
end

def to_nat (n : Natural) : Nat := match n with
  | .inl k => Ev.to_nat k
  | .inr k => Od.to_nat k

#eval to_nat (of_nat 16) -- 16

#eval of_nat (to_nat (of_nat 3))  -- Sum.inr (Od.succ (Ev.succ (Od.succ (Ev.zero))))
```

Left Inverse
===

To build out the equivalence, we first show that `of_nat` is a left inverse of `to_nat`.

By the way, theorems can be *mutually defined*!


```lean
mutual

  @[simp]
  theorem Ev.left_inv {ev : Ev} : of_nat (Ev.to_nat ev) = Sum.inl ev := by
    cases ev <;> simp[Ev.to_nat,of_nat,succ,Od.left_inv,zero]

  @[simp]
  theorem Od.left_inv {od : Od} : Natural.of_nat (Od.to_nat od) = Sum.inr od := by
    cases od; simp[Od.to_nat,of_nat,succ,Ev.left_inv]

end

theorem left_inv {n : Natural} : Natural.of_nat n.to_nat = n := by
    cases n with
    | inl _ => exact Ev.left_inv
    | inr _ => exact Od.left_inv
```

Right Inverse
===

Next we show `to_nat` is a right inverse of `of_nat`.


```lean
@[simp]
theorem to_nat_succ {m : Natural}
  : m.succ.to_nat = m.to_nat.succ := by
  cases m <;> aesop

@[simp]
theorem right_inv {n : Nat} : (Natural.of_nat n).to_nat = n := by
  induction n with
    | zero => aesop
    | succ n ih =>
      unfold Natural.of_nat -- common pattern in induction. required for ih to apply.
      conv =>
        rhs
        rw[←ih]
      rw[to_nat_succ]
```

The Equivalence
===

Finally we have the desired equivalence.

```lean
def equiv_nat : Natural ≃ Nat:= {
  toFun := Natural.to_nat,
  invFun := Natural.of_nat,
  left_inv _ := left_inv,
  right_inv _ := right_inv
}
```
 Here's an example of transporting addition and multiplication from `Nat` to `Natural`.  
```lean
instance add : Add Natural := equiv_nat.add
instance mul : Mul Natural := equiv_nat.mul

def three := of_nat 3
def twelve := of_nat 12
def thirteen := of_nat 13

#eval to_nat (three * ( twelve + thirteen ) )     -- 75
```

Exercise
===

<ex /> Show


```lean
def spin_bool_equiv : Spin ≃ Bool := sorry
```

Exercise
===

<ex /> (Optional) Consider the following two types for the complex numbers.


```lean
structure K1 where
  re : ℝ
  im : ℝ

structure K2 where
  a : ℝ
  θ : ℝ
  pa := 0 ≤ a
  pθ := 0 ≤ θ ∧ θ < 2*Real.pi
  h : a = 0 → θ = 0
```
 Define the natural equivalence  
```lean
def K_equiv : K1 ≃ K2 := sorry

--hide
end Natural
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

