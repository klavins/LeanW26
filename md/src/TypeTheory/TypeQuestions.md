
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

**VAR**: If a context defines `x` to have type `τ` then (somewhat obviously)
we can conclude `x` has type `τ`.

**ABST**: If our context defines `x : σ` and allows us to conclude that
`M : τ`, then we can form an abstraction from `x` and `M` that has type `σ` to `τ`.

**APPL**: If `Γ` allows us to conclude both that `M : σ→τ` and `N : σ`,
then the application of `M` to `N` has type `τ`.

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
```
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



License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

