
Type Inference
===

Type Theory Questions
===

**TYPE INFERENCE**: Can M be assigned a type consistent with a given context?
```lean
Γ ⊢ M : ?
```

**TYPE CHECKING**: In a given context, does a term M have a given type σ?
```lean
Γ ⊢ M : σ
```

**WELL TYPEDNESS**: Does there exist a context in which a type be assigned to a
term M? Another way of saying this is "is M a legal term?"
```lean
? ⊢ M : ?
```

**INHABITATION**: Does there exist a term of a given type? If σ is a logical
statement, then this is the question of whether σ has a proof.
```lean
Γ ⊢ ? : σ
```


Statements, Contexts, and Judgements
===

Definitions

- A **type statement** is a pair `x : σ` where `x` is a type variable and `σ`
is a type. We say "`x` is of type `σ`".

- A **typing context** `Γ` is a finite set of type state statements.

- A **judgement** is an expression of the form `Γ ⊢ M : σ` where `Γ` is a
typing context, `M` is a simply typed λ-calculus statement, and `σ` is a
type. When `Γ ⊢ M : σ` we say `Γ` allows us to conclude that `σ` has type `M`.

For example, here is a judgment that states: "When `f` is a function
from `α` to `β` and `x` is of type `α`, then `f x` is of type `β`. "
```none
{ f : α → β, x : α }  ⊢ f x : β
```

The symbol `⊢` is entered equivalently (and suggestively) as `\entails` or `\goal`.

Typing Rules
===

Typing rules are written the same way as the inference rules in propositional logic.
```none
  VAR   ————————————————
          Γ,x:τ ⊢ x:τ

               Γ,x:σ ⊢ M : τ
  ABST  ——————————————————————————
           Γ ⊢ (λ x:σ => M) : σ→τ

           Γ ⊢ M : σ→τ    Γ ⊢ N : σ
  APPL  ——————————————————————————————
                   M N : τ
```

**VAR**: If a context defines `x` to have type `τ` then
`x` has type `τ`.

**ABST**: If our context defines `x : σ` and allows us to
conclude that `M : τ`, the abstraction formed from `x` and `M`  has type `σ` to `τ`.

**APPL**: If `Γ` allows us to conclude both that `M : σ→τ`
and `N : σ`, then the application of `M` to `N` has type `τ`.

Example
===

Q: Find the type of
```none
λ x : A => x
```

A: Working backwards from this goal we use ABST with `τ=A` and `M=x` to get
```none
x:A ⊢ x:A
```

Then we use VAR. So the expression has type `A→A` and a proof of this is:
```none
1) x:A ⊢ x:A                  by VAR
2) (λ x : A => x) : A→A       by ABST
```

As we have seen, Lean figures this out automatically. 
```lean
#check fun x : _ => x           -- ?m.1 → ?m.1
```

Example
===

Find the types of `x` and `y` in
```none
λ x => λ y => x y
```

Using ABST twice with hypothized types `A`, `B`, and `C` we get
```none
x : B   ⊢  λ y => x y : A
x : B, y : C   ⊢  x y : A
```

Next we use the APPL rule with `M = x`, `N = y`, `σ = C`, `τ = A`
```none
x : B, y : C  ⊢  x : C → A
x : B, y : C  ⊢  y : C
```

These judgements would hold if `B` were equal to `C→A`.
```none
λ x : C → A => λ y : C => x y
```

for some types `C` and `A`.

Derivation Tree
===

Following the derivation above in reverse gives the following type inference proof tree:
```none
    ————————————————————————————— VAR    ————————————————————————————— VAR
     x : C → A, y : C  ⊢  x : C → A       x : C → A, y : C  ⊢  y : C
    ———————————————————————————————————————————————————————————————————— APPL
                      x : C → A, y : C   ⊢  x y : A
                 ————————————————————————————————————————— ABST
                    x : C → A  ⊢  λ y : C => x y : C → A
            ————————————————————————————————————————————————————— ABST
             ⊢  λ x : C → A => λ y : C => x y : (C → A) → C → A
```

Thus, the type of `λ x => λ y => x y` is `(C → A) → C → A`.

Lean can figure this out for us, but we do need to tell it that `x` is a
function type of some kind. 
```lean
#check fun x : _ → _ => fun y : _ => x y      -- (?m.4 → ?m.2) → ?m.4 → ?m.2
```

Dependent Types Subsume Simple Types
===

The main inference rules for dependent types are
```none
          Γ ⊢ A : U    Γ, x:A ⊢ B : U
Π-Form   ——————————————————————————————
              Γ ⊢ (Π x:A, B) : U


             Γ, x:A ⊢ b : B
Π-Intro  ————————————————————————   (ABST when B does not depend on A)
          Γ ⊢ λ x ↦ b : Π x:A, B


           f : Π x:A, B    Γ ⊢ a : A
Π-Elim   ———————————————————————————— (APP when B does not depend on A)
              Γ ⊢ f a : B[a/x]
```

The first rule descibes how to form new types, such as `Π n : Nat, Vector ℝ n`.

The second two describe abstraction and application for dependent types.



Example
===

Consider

```lean
#check (fun n : ℕ => Vector.replicate n 0) 3       -- Vector ℕ 3
```


How does Lean infer this type?

- `fun n : ℕ => Vector n` is a type via `Π-Form`.
- The abstraction `fun n : ℕ => Vector.replicate n 0` is a term of this type by `Π-Intro`.
- The whole expression has the form type `Vector ℕ 3` by `Π-Elim`.



Inductive Types
===
For each constructor of an inductive type you get an inference rule describing how
to form new elements of the type. For example, with `Nat`:

```none

                                                   Γ ⊢ n : Nat
  Nat-Intro₁  ——————————————       Nat-Intro₂   —————————————————
              Γ ⊢ zero : Nat                     Γ ⊢ n.succ : Nat
```

We have already encounterd the elimination rule, which is  `.rec` For example, with
`Nat` we can write `.rec` inference rule style as something like.

```none
            Γ ⊢ m : Nat → Sort u   Γ ⊢ m 0    Γ, Π n:Nat, Π m n, m n.succ
 Nat-Elim   ———————————————————————————————————————————————————————————————
                            Γ, t:Nat ⊢ motive t
```

What's cool is that you can basically program Lean's type inference engine
(the kernel) with new inference rules by defining inductive types.



Lean's Kernel
===

Lean's Kernel is C++ code the implements type inference and type checking.
It follows essentially the procedure we outlined above. If you look in

```none
https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp
```

for example, you will find methods named
```none
infer_fvar                infer_constant         infer_lambda
infer_pi                  infer_app              infer_let
infer_proj                infer_type_core        infer_type
```
All user defined types, syntax, macros, etc. are compiled into the term level
before sending to the kernel. If the kernel gives an error, it could be your code
or the higher level Lean code that produces the term level code.

Lean's Kernel is small enough to be **auditable**, meaning you can try to model it
in a proof assistant ... like lean.

For example: [https://github.com/digama0/lean4lean](https://github.com/digama0/lean4lean).



Type Inference and Well Typedness
===

The problems `Γ ⊢ M : ?` and `? ⊢ M : ?` can easily be managed
by Lean's type checker.

```lean
#check (fun x => x)   -- ?m.1 → ?m.1 Lean makes up a type for x so
                      -- the whole expression has a type
```
 This is also happening when you make new definitions without
providing types. 
```lean
def f (L : List ℕ) := L.reverse.cons 0

#check f     -- List ℕ → List ℕ
```

Type Checking
===
The problem `Γ ⊢ M : σ` amounts to making sure you didn't make a
mistake in writing out the type of an expression.

```lean
#check ((fun x : Nat => x) : Nat → Nat)  -- Lean checks whether the type
                                         -- provided is legit.
```
 This is essentially what proof assistants do: Check your work. 

Inhabitation
===
The problem `Γ ⊢ ? : σ` amounts to *synthesizing* a term of a given type.
It requires searching over *all* terms of which there are an infinite number.
Thus, this problem is beyond intractable. It is *undecidable*.

But Lean has some search algorithms for simple types.

```lean
def thm (n : Nat) : n+1 > 0 :=     -- The aesop tactic finds a
  by aesop                                -- term of the desired type

#print thm
```
 This doesn't always work: 
```lean
def goldbach : ∀ n : ℕ, n > 2 ∧ Even n →
               ∃ p q : ℕ, Nat.Prime p ∧
                          Nat.Prime q ∧
                          p + q = n :=
  by aesop
```

```none
aesop: failed to prove the goal after exhaustive search
```

Keeping mathematicians in business (for now).


Exercises
===

<ex /> Type Inference: Show that the expression `fun x => fun f => f x` has type `A → (A → B) → B` for some types `A` and `B` using a derivation tree like the one on slide 6 of this slide deck.

<ex /> Inhabitation: Suppose

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons {n} :  α → Vec α n → Vec α (n + 1)
```
 Construct a terms (function definitions) that type check
to replace the `sorry` in each of the following definitions.

```lean
def g1 : ℕ → Vec ℕ 0 := sorry
def g2 : Σ n, Vec ℕ n := sorry
def g3 : Π f : ℕ → ℕ, Σ n, Vec ℕ (f n) := sorry
def g4 : Σ A, Π B, Vec A B := sorry


--hide
end LeanW26.Inference
--unhide
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

