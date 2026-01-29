
Propositional Logic
===

Goal
===

The goal of this slide deck is to introduce the propositional logic as a formal mathematical
object. Although there are a few Lean examples here, most of this slide deck is
pencil and paper work.

Specifically we introduce
- Logical contexts
- Proof states
- Inference rules
- Formal proofs

The results presented here can be extended to any formal mathematical
system, such as first order logic, higher order logic, type theory, etc.




Propositions
===

A **proposition** is a statement that is either true or false. The following are examples:

- It is raining outside.
- All cats are animals.
- Darth Vader is Luke's Father.
- Four is greater than five.

In propositional logic, we assign **propositional variables** to represent
the value of these statements. So we might make the assignments:

- p := It is raining outside.
- q := All cats are animals.
- r := Darth Vader is Luke's Father.
- s := Four is greater than five.

In Lean, we declare propositional variables as follows: 
```lean
variable (p q r s : Prop)
```

Atomic vs Compound Propositions
===

A proposition that corresponds to a direct measurement or other basic truth
is called **atomic**. It cannot be sub-divided into more basic propositions.
Otherwise it is called compound. For example, the proposition

- It is raining outside or all cats are animals.

is a compound proposition that uses the _connective_ "or", written as `∨` to
connect two atomic propositions. Symbolically, we write 
```lean
#check p ∨ q
```
 to check that the compound `p ∨ q` is a proposition. 

Notation
===

Students used to digital logic will wonder why we are using `∨` instead of the symbol `+`.
The main reason is that `+` will usually mean actual addition when things get more complicated.
Thus, mathematicians have invented new symbols for logical connectives.
Here are the most important for our current purposes: 
```lean
#check ¬p               -- not p
#check p ∨ q            -- p or q
#check p ∧ q            -- p and q
#check p → q            -- p implies q
#check p ↔ q            -- p if and only if q
#check True
#check False
```

Shorthand
===

We also have the propositional `False` which denotes **absurdity**.
In _Intuitionistic Logic_, `¬p` is shorthand for

```
p → False
```

```lean
#check False
#check p → False
```

If and only if, `↔`, is shorthand for `→` in both directions
```
p ↔ q  ≡  p → q ∧ q → p
```

Constructive Proofs
===

The goal is this slide deck is to define a mathematical framework in which we
prove statements by constructing proofs.

In particular, to prove

- `p ∧ q`, construct a proof of p and another proof of `q`.
- `p ∨ q`, construct a proof of p or we construct a proof of `q`.
- `p → q`, supply a method for converting a proof of `p` into a proof of `q`
- `¬p`, supply a method to convert a proof of `p` to a proof of `⊥`



Comparison to Classical Logic
===

We have defined **intuitionistic** logic or **constructive logic**,
different from **classical logic**. In classical logic, the truth of a statement like
```none
p ∨ ¬p
```
is guaranteed by the **law of the excluded middle**.
In constructive mathematics, you have to either
construct a proof of `p` or construct a proof of `¬p`. As an example:

> 1) The universe is infinite or the universe is finite.

Neither option currently has a proof.
Classically, we would still conclude it is true, but constructively
we are just stuck. Similarly,

> 2) P = NP or P ≠ NP

> 3) There are either a finite number of twin primes, or an infinite number of twin primes.

These statements may be proved some day, but for now,
we cannot conclude they are true using constructive mathematics.

Double Negation
===

Similar to the law of the excluded middle is double negation:
```
¬¬p ↔ p
```
Classically, this is a tautology (a proposition that is always true).
But constructively, from a proof of "it is not the case that p is not true"
one cannot necessarily construct a proof that `p` is true.

As a result, `proof by contradiction` is not valid constructively,
because in proof by contradiction one follows the procedure:
```none
To prove `p`, assume `¬p` and derive `False`.
```
Just because we have a way to transform a proof of `¬p` into `False`
does not mean we can have a construction of a proof of `p`.


Classical Logic in Lean
===

As an aside, Lean can reason both classically and constructively.


```lean
theorem t (p : Prop) : p ∨ ¬p :=
  Classical.em p

#print axioms t  -- 'LeanW26.t' depends on axioms: [propext, Classical.choice, Quot.sound]
```

We'll get to this later.


Exercise
===

<ex /> Which of the following two statements
if any cannot be proven without the law of the excluded middle?
- `p ∨ (q∧r) → (p∨q) ∧ (p∨r)`
- `(p∨q) ∧ (p∨r) → p ∨ (q∧r)`
- `((p→q)→p)→p`


Contexts
===

We now begin to build a framework for proving theorems in propositional logic.
The first thing we need is a way to keep track of what propositions we
currently know in the course of proving something.

To this end we define a **context** to be a finite set of propositions.
Given two contexts `Γ` and `Δ` we can take their union `Γ ∪ Δ` to make
a new context. The notation is a bit cumbersome, so we write `Γ,Δ` instead.
In particular, if `φ ∈ Φ` then `Γ,φ` is shorthand for `Γ ∪ {φ}`.

If we can show that a proposition `φ` is true whenever all the propositions
in a context `Γ` are true, we write
```
Γ ⊢ φ
```
which reads gamma `entails` `φ`.


Tautologies
===

If a proposition `φ` is tautology
(meaning it is always true like `p ↔ p`) then it is true independent of any context.
That is, the empty context entails any tautology. Thus, we write
```
⊢ φ
```
to mean `∅ ⊢ φ`. We will define precisely what the entails relationship means next.



Rules of Inference
===

A **rule of inference** is set of **premises** and a **conclusion** that can be drawn
from those premises.

Rules are presented with a name
followed by what looks like a fraction with the premises listed on top and the
conclusion on the bottom.
```none
                Γ₁ ⊢ A    Γ₂ ⊢ B    Γ₃ ⊢ C
  RULE NAME    ————————————————————————————
                          Γ ⊢ D
```
In this schematic, the rule has three premises, each of which describe an assumption
that a particular context entails a particular proposition. And the rule has one conclusion,
stating the entailment you are allowed to conclude.

Usually, the contexts listed and the propositions are related in some way.


Propositional Axioms
===

The first rule has no premises and simply states that `φ` can be concluded from any
context containing φ. Said constructively, if we have a proof of `φ`, then obviously
we can construct a proof of `φ`.
```none
  AX  ——————————
       Γ,φ ⊢ φ
```

For example, if `p` is a proposition and our context is `Γ = {p}`, then we can conclude `p`,
and we write

```none
{p} ⊢ p
```


Implies Rules
===

We have two rules for the `→` connective:
```none
              Γ,φ ⊢ ψ
  →-Intro   ————————————
             Γ ⊢ φ → ψ

            Γ ⊢ φ → ψ    Γ ⊢ φ
  →-Elim   —————————————————————
                 Γ ⊢ ψ
```
The **Implies Introduction** rule allows us to introduce `φ → ψ` whenever we have `Γ` and
`φ` together entailing `ψ`.

**Implies Elimination** is also know as **Modus Ponens**.
It states that if we know `φ` implies `ψ` and we know `φ`, then we know `ψ`.

Implies is written with exactly the same arrow `→` as a function type.
A proof of `φ→ψ` is a function that converts proofs of `φ` into proofs of `ψ`.
To prove statements with implications we thus use λ-calculus expressions
(which have arrow types).


Implication Intro Example
===

**`→-Intro` is lambda abstraction:**
The context includes a proof of `p`. Thus we can _introduce_ `q→p` for any `q`.
We do this with a lambda expression taking a proof of `q` (and in this case ignoring it)
and returning the proof `hp` of `p` available in the context.

**Example**: Prove `{p} ⊢ q → p`

**Proof**: Since `{p,q} ⊢ p` holds by the `Axiom` rule we can conclude `{p} ⊢ q → p` by `→-Intro`.

**Note:** We usually search from the goal backwards.
- Encountering the goal `q → p`, we posit it was obtained by some proof ending with `→-Intro`.
- _Applying_ `→-Intro` to the proof state `{p} ⊢ q → p` yields the simply proof state `{p,q} ⊢ p`,
which we can prove using `Axiom`.
- Thus, proving amounts to searching for a sequence of rule applications starting with the goal and
going back to axioms.



Implication Elimination Example
===

**`→-Elim` is lambda application:**
We have a context with a proof of `p→q` and a proof of `p`.
We know the proof `hp` of `p→q` is a lambda abstraction.
So we can apply it to a proof `hp` of `p` to get a proof of `q`.

**Example:** Prove `{p → q, p} ⊢ q`

**Proof**: Apply `→-Elim` with `φ=p` and `ψ=q`, yielding sub-goals:
- Goal 1: `{p → q, p} ⊢ p → q`
    - Apply `Axiom`
- Goal 2 :`{p → q, p} ⊢ p`
    - Apply `Axiom`



Exercise
===

<ex /> Prove `⊢ (p → q) → p → q` by hand in the format described in this slide deck.


And Rules
===

Next we have three rules for the ∧ connective:
```none
              Γ ⊢ φ   Γ ⊢ ψ
  ∧-Intro  ———————————————————
               Γ ⊢ φ ∧ ψ

                  Γ ⊢ φ ∧ ψ
  ∧-Elim-Left   ——————————————
                    Γ ⊢ φ

                  Γ ⊢ φ ∧ ψ
  ∧-Elim-Right  —————————————
                    Γ ⊢ ψ
```

**And Introduction** rule says we can construct a proof of `φ ∧ ψ` whenever the context
contains a proof of `φ` and a proof of `ψ`.

**And Elimination** rules allow us to "eliminate" half of the proposition `φ ∧ ψ` to conclude
the weaker statement `φ` or the weaker statement `ψ`.


And Example
===

**Example**: Show `{p∧q} ⊢ q∧p`

**Proof**:
- Apply ∧-Intro to get sub-goals:
    - Goal 1: `{p∧q} ⊢ q`
        - Apply `∧-Elim-Right`
    - Goal 2: `{p∧q} ⊢ p`
        - Apply `∧-Elim-Left`

Or Rules
===

Then we have three rules for the ∨ connective:
```none
                   Γ ⊢ φ
 ∨-Intro-Left   ———————————
                 Γ ⊢ φ ∨ ψ

                    Γ ⊢ ψ
 ∨-Intro-Right   ————————————
                  Γ ⊢ φ ∨ ψ

            Γ ⊢ φ ∨ ψ    Γ ⊢ φ → ρ    Γ ⊢ ψ → ρ
 ∨-Elim   ———————————————————————————————————————
                         Γ ⊢ ρ
```

**Or Introduction** allows us to conclude `φ ∨ ψ` from one of its parts.

**Or Elimination** says that if we know `Γ ⊢ φ ∨ ψ` then we know that `Γ` must
entail either `φ` or `ψ`.
If we also know that both `φ` and `ψ` separately entail `ρ`, then we know that `Γ` must entail `ρ`.


Or Example
===

**Example**: Show `{p∨q} ⊢ q∨p`

**Proof**:
- Apply `∨-Elim` with `φ=p`, `ψ=q` and `ρ = q∨p` to give three sub-goals
    - Goal 1: `{p∨q} ⊢ p∨q`
        - Apply `Axiom`
    - Goal 2: `{p∨q} ⊢ p → q∨p`
        - Apply `→-Intro` to get the sub-goal `{p∨q,p} ⊢ q∨p`
        - Apply `∨-Intro-Right`
    - Goal 2: `{p∨q} ⊢ q → q∨p`
        - Apply `→-Intro` to get the sub-goal `{p∨q,q} ⊢ q∨p`
        - Apply `∨-Intro-Left`

Exercise
===

<ex /> Prove `⊢ p ∧ q → p ∨ q` by hand in the format described in this slide deck


Ex Falso
===

Finally, we have the a rule for the ¬ connective:
```none
                  Γ ⊢ ⊥
  False -Elim ————————————
                  Γ ⊢ φ
```

which states that you can conclude anything if you have a proof of ⊥.
This rule is also know as **ex falso sequitur quodlibet** or just **ex falso**.

Example with False
===

**Example:** ∅ ⊢ (p → q) → (¬q → ¬p)

**Proof:**
- Apply `→-Intro` twice to get `{p→q,¬q} ⊢ ¬p`
- Recalling the definition of `¬` in terms of `→`, apply `→-Intro` again to get `{p→q,¬q,p} ⊢ ⊥`.
- Expand the definition of `¬` again to get `{p→q,q→⊥,p} ⊢ ⊥`
- Use `→-Elim` to get sub-goals
    - Goal 1: `{p→q,q→⊥,p} ⊢ q→⊥`
        - Apply Axiom
    - Goal 2: `{p→q,q→⊥,p} ⊢ q`
        - Apply `→-Elim` to get sub-goals
            - Goal 2a: `{p→q,q→⊥,p} ⊢ p→q`
                - Apply `Axiom`
            - Goal 2b: `{p→q,q→⊥,p} ⊢ p`
                - Apply `Axiom`


Proofs in General
===

**Def:** A **proof** of `Γ ⊢ φ` is a tree where
- each node is a proof state form `Γ' ⊢ φ'`
- each parent follows from its children via a a proof rule.

**Observations**
- Constructing this proof is a purely syntactic endeavor.
- One can easily imagine an algorithm that does this automatically by
pattern matching the  against the `Γ`, `φ`, `ψ`, `ρ` in each inference rule
- We can add more inference rules for Objects, functions, Quantifiers, etc.
- As we add complexity, finding a proof goes from intractable to undecidable
- But checking a proof is linear in the number of steps.



<div class='fn'>E.g. "This sentence is not provable in Lean" can in principle
be formalized in Lean. Or the continuum hypothesis, once ZF is encoded in Lean.</div>

Exercises
===

<ex /> Prove both directions of `∨` distributing over `∧`
- `⊢ p ∨ (q∧r) → (p∨q) ∧ (p∨r)`
- `⊢ (p∨q) ∧ (p∨r) → p ∨ (q∧r)`

<ex /> Prove the statement `(¬¬p) ↔ p` (by hand) in the format described in this slide deck.
One direction requires classical logic.
For that direction, formally state the law of the excluded
middle as an inference rule and use the rule in your proof.







References
===

- Morten Heine Sørensen, Pawel Urzyczyn. "Lectures on the Curry-Howard Isomorphism".
Elsevier. 1st Edition, Volume 149 - July 4, 2006.


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

