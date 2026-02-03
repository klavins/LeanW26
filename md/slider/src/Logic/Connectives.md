
Propositional Connectives
===

Overview
===
Inductive types capture all of propositional logic, first order logic, and more.

Instead of defining _and_, _or_ and the other logical connectives as
built-in operators in CIC, they are just defined terms of more primitive inductive types.

In this slide deck we redefine the connectives, to understand how they work.
To avoid naming conflicts with Lean's standard library, we open a namespace.


```lean
namespace Temp
```
 And we define some variables to use throughout. 
```lean
variable (p q r : Prop)
```
 We begin by reviewing what we have previous covered about propositional logic. 

The Axiom Rule
===

Not to be confused with Lean's `axiom` keyword.

As discussed in the slide deck on Propositional Logic, the Axiom Rule is

```none
  AX  ——————————
       Γ,φ ⊢ φ
```
Here is a proof of `{hp:p} ⊢ p` in Lean using the Axiom rule: 
```lean
example (hp : p) : p :=  hp
```
 Putting your cursor at the beginning of the second like, you will see
```
hp : p
⊢ p
```
Which says, given we have a proof `hp` of `p`, we need show `p`.
This is easy, we just use `hp` itself.


Aside: def, theorem, example, lemma
===

By the CHI, note that `def` and `theorem`
are essentially the same from a type theory point of few. And `example` is
just a definition without a name.

So in the above we could write:


```lean
def prop_id (hp : p) := hp

theorem prop_id_thm (hp : p) : p := hp

example (hp : p) : p := hp
```
 Also, `prop_id` is really just a special case of the identity function. 
```lean
def my_id.{u} {α : Sort u} (x : α) : α := x

example (hp : p) : p := my_id hp
```
 Finally, example is not just for `Prop`: 
```lean
example : Nat := 10000001
```

Implication in Lean
===

**`→-Intro` is lambda abstraction:** Whenever you see a goal of the form `A → B`, you
write a lambda to get a simpler goal.

```lean
example (hp : p) : q → p :=
  fun hq => sorry                           -- goal for the `sorry` is `p`

example (hp : p) : q → p :=
  fun hq => hp
```

**`→-Elim` is lambda application:** When you see function (with type `A → B`) in a context
you can apply it to get a simpler goal.

```lean
example (hpq : p → q) (hp : p) : q :=
  hpq sorry                                 -- goal for the `sorry` is `p`

example (hpq : p → q) (hp : p) : q :=
  hpq hp
```

And is an Inductive Type
===

Recall the inference rule
```none
              Γ ⊢ p   Γ ⊢ q
    ∧-Intro ———————————————————
                Γ ⊢ p ∧ q
```

It states that whenever we know propositions `p` and `q`, then we know `p ∧ q`.
From the point of view of types,
it says that if `p` and `q` are of type `Prop`, then so is `p ∧ q`.

We can write this as an inductive type definition as follows. 
```lean
inductive And (p q : Prop) : Prop where
  | intro : p → q → And p q
```
 You can think of `h : And p q` as
- `h` has type `And p q`
- `h` is evidence that the type `And p q` is not empty
- `h` is a proof of the proposition `And p q`.

Proof of a Simple Proposition
===

Consider the proposition
```lean
q → p → And p q
```

As a type, this proposition is a function from `q` to `p` to `And p q`.
Thus, we know that an element of this type has the form
```lean
fun hq => fun hp => sorry
```

For the body of this lambda abstraction, we need to *introduce* an `And` type,
which requires proofs of `q` and `p` respectively. Using the inductive definition of `And` we get
```lean
fun hq hp => And.intro hp hq
```

The complete proof is then:

```lean
example : q → p → And p q :=
  fun hq => fun hp => And.intro hp hq
```

And Elimination
===

The elimination rules for `And` are
```none
                Γ ⊢ p ∧ q                          Γ ⊢ p ∧ q
  ∧-Elim-Left ——————————————         ∧-Elim-Right —————————————
                  Γ ⊢ p                              Γ ⊢ q
```
which we can write in Lean as 
```lean
def And.left {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro hp _ => hp

def And.right {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro _ hq => hq
```

Proofs with And-Elimination
===

With these inference rules, we can do more proofs: 
```lean
example : (And p q) → (And q p) :=
  fun hpq => And.intro hpq.right hpq.left
```

Match is Enough
===

The elimination rules above are a _convenience_ we defined to make the proof look
more like propositional logic. We could also have written: 
```lean
example (p q : Prop) : (And p q) → p :=
  fun hpq =>
  match hpq with
  | And.intro hp _ => hp
```
 You can view `match` as a generic elimination rule. 

Lean's And
===

Lean's And is actually defined as a structure:
```lean
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```

The `intro ::` part renames the introduction rule `intro` instead of the default `mk`.

Lean defines infix notation `∧`. So you can write


```lean
--hide
end Temp -- stop using our temporary namespace and use Lean's And
variable (p q r : Prop)
--unhide


#check p ∧ q                        --p ∧ q : Prop
```

Structures
===
With Lean's `And` defined as a structure we can do

```lean
example : (p ∧ q) → (q ∧ p) :=
  fun hpq => And.intro hpq.right hpq.left

example : (p ∧ q) → (q ∧ p) :=
  fun hpq => { left := hpq.right, right :=  hpq.left }

example : (p ∧ q) → (q ∧ p) :=
  fun hpq => ⟨ hpq.right, hpq.left ⟩
```
 You can match the the parts of a structure in the argument to `fun`: 
```lean
example : (p ∧ q) → (q ∧ p) :=
  fun ⟨ hp, hq ⟩ => ⟨ hq, hp ⟩
```

Exercise
===

<ex /> Show the following using a term level proof without using the library.


```lean
example : p ∧ (q ∧ r) → (p ∧ q) ∧ r := sorry

--hide
namespace Temp
--unhide
```

Or is Inductive
===

To introduce new `Or` propositions, we use the two introduction rules
```none
                 Γ ⊢ p                              Γ ⊢ p
 ∨-Intro-Left ———————————          ∨-Intro-Right ————————————
               Γ ⊢ p ∨ q                          Γ ⊢ p ∨ q
```
In Lean, we have 
```lean
inductive Or (p q : Prop) : Prop where
  | inl (h : p) : Or p q
  | inr (h : q) : Or p q
```
 For example,  
```lean
example : And p q → Or p q :=
  fun ⟨ _, hq ⟩ => Or.inr hq
```

Or Elimination
===

Recall the inference rule
```none
           Γ,p ⊢ r    Γ,q ⊢ r    Γ ⊢ p ∨ q
  ∨-Elim ————————————————————————————————————
                       Γ ⊢ r
```

It allows us to prove `r` given proofs that `p → r`, `q → r` and `p ∨ q`.

We can define this rule in Lean with: 
```lean
def Or.elim {p q r : Prop} (hpq : Or p q) (hpr : p → r) (hqr : q → r) :=
  match hpq with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq
```

Example of and Or-Elim Proof
===

Here is an example proof using or introduction and elimination. 
```lean
example : Or p q → Or q p :=
  fun hpq => Or.elim
      hpq                                 -- ⊢ p ∨ q
      (fun hp => Or.inr hp)               -- ⊢ p → (q ∨ p)
      (fun hq => Or.inl hq)               -- ⊢ q → (q ∨ p)
```
 Once again, the elimination rule is just a convenience.
The proof could have been written with `match`. 
```lean
example : Or p q → Or q p :=
  fun hpq =>
  match hpq with
  | inl hp => Or.inr hp
  | inr hq => Or.inl hq
```

True is Inductive
===
`True` is defined inductively as
```lean
inductive True : Prop where
  | intro : True
```

for example:


```lean
example : Or True True := Or.inl True.intro
```
 Or, using Lean's notation and definitons 
```lean
--hide
end Temp
--unhide

#print trivial                 -- theorem trivial : True := True.intro

example : True ∨ True := Or.inl trivial

--hide
namespace Temp
--unhide
```

False is Inductive
===

Finally, we have `False`, which has no introduction rule, kind of like `Empty`,
except we add the requirement that `False` is also type of `Prop`.  
```lean
inductive False : Prop
```
 From `False` we get the `Not` connective, which is *syntactic sugar*. 
```lean
def Not (p : Prop) : Prop := p → False
```
 Here is an example proof: 
```lean
example : (p → q) → (Not q → Not p) :=
  fun hpq hq =>
  fun hp =>
  hq (hpq hp)
```

False Elimination
===

To define the elimination rule for `False`
```
           Γ ⊢ ⊥
  ⊥-Elim ——————————
           Γ ⊢ p
```
we take advantage of the fact that `False` was defined inductively. 
```lean
def False.elim {p : Prop} (h : False) : p :=
  nomatch h
```
 Here is an example proof that from False you can conclude anything: 
```lean
example (p q : Prop) : And p (Not p) → q :=
  fun ⟨ hp, hq ⟩ => False.elim (hq hp)
```
 This elimination rule provides another way to prove the example: 
```lean
example : False → True :=
  False.elim
```

If and only iff
===

If and only if is defined inductively as
```lean
structure Iff (p q : Prop) : Prop where
  intro ::
  mp : p → q → Iff p q
  mpr : q → p → Iff q p
```

with notation `p ↔ q`.

For example:


```lean
example : p ↔ p := Iff.intro id id
```
 or 
```lean
example : p ↔ p := { mp := id, mpr := id }
```
 or 
```lean
example : p ↔ p := ⟨ id, id ⟩
```

Notation
===

Lean defines notation like `∨` and `∧` for logic to make it look like math.
We won't redo that entire infrastructure here.
But to give a sense of it, here is how Lean defines infix
notation for `Or`, `And`, and `Not` notation.

```hs
infixr:30 " ∨ "  => Or
infixr:35 " ∧ "   => And
infixr:50 " ↔ "   => Iff
notation:max "¬" p:40 => Not p
```

The numbers define the precedence of the operations. So `v` has lower precedence than `∧`,
which has lower precedence than `¬`.

Now we can write: 
```lean
--hide
end Temp -- start using Lean's propositions
--unhide

example (p q : Prop) : (p ∧ (¬p)) → q :=
  fun ⟨ hp, hnp ⟩ => False.elim (hnp hp)
```

<div class='fn'>
  <a href="https://github.com/leanprover/lean4/blob/master/src/Init/Notation.lean">
  Lean's core notation</a></div>



Exercise
===

<ex /> Show


```lean
example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := sorry
```

<ex /> Do all these proofs, which are borrowed from the [Theorem Proving in Lean Book](https://lean-lang.org/theorem_proving_in_lean4/title_page.html). Use only term level proofs. No tactics.


 
```lean
example : p ∨ q ↔ q ∨ p := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬(p ∧ ¬p) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
```

<ex /> This one requires the law of the excluded middle, which can be
used with `Classical.em`. The way to do this one is to do Or-elimination
on `Classical.em p`.

```lean
example : (p → q) → (¬p ∨ q) := sorry
```

Exercise
===

<ex /> Consider the Not-Or operation also known as Nor. It has the following inference rules:
```none
             Γ ⊢ ¬p   Γ ⊢ ¬q
  Nor-Intro ———————————————————
               Γ ⊢ Nor p q


                 Γ ⊢ Nor p q                          Γ ⊢ Nor p q
  Nor-Elim-Left ——————————————         Nor-Elim-Right —————————————
                   Γ ⊢ ¬p                                Γ ⊢ ¬q

```
Define these in Lean. Here is a start:


```lean
inductive Nor (p q : Prop) : Prop where
  | intro : ¬p → ¬q → Nor p q

def Nor.elim_left {p q : Prop} (hnpq : Nor p q) : Prop := sorry
def Nor.elim_right {p q : Prop} (hnpq : Nor p q) : Prop := sorry
```

Exercise
===

<ex /> Use your `Nor` inference rules, and the regular inference rules from Lean's
propopsitional logic, to prove the following examples.



```lean
example : ¬p → (Nor p p) := sorry
example : (Nor p q) → ¬(p ∨ q) := sorry
example : ¬(p ∨ q) → (Nor p q) := sorry
```

References
===

- Section 7.3 of [TPL](https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html) describes how to define the propositional connectives.


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

