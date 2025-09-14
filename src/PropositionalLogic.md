
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/PropositionalLogic.lean'>Code</a> for this chapter</span>
 # Propositional Logic

## Propositions

A **proposition** is a statement that is either true or false. The following are examples:

- It is raining outside.
- All cats are animals.
- Darth Vader is Luke's Father.
- Four is greater than five.

In propositional logic, we assign **propositional variables** to represent the value of these statments. So we might make the assignments:

- p := It is raining outside.
- q := All cats are animals.
- r := Darth Vader is Luke's Father.
- s := Four is greater than five.

In Lean, we declare propositional variables as follows: 
```lean
variable (p q r s : Prop)
```
 Note that we are not saying p is the English language sentence "It is raining outside". We are not doing natural language processing here. Rather, we are saying that `p` is a **propositional variable** that is true when it actually is raining outside, and false otherwise. To determine the truth value of `p`, we would need some way to check whether it is raining outside (as well as some specifics like outside _where_ and _when_? For now, we'll just be informal about such things).

## Atomic vs Compound Propositions

A propsition that corresponds to a direct measurement or other basic truth is called **atomic**. It cannot be sub-divided into more basic propositions. Otherwise it is called compound. For example, the proposition

- It is raining outside or all cats are animals.

is a compound proposition that uses the _connective_ "or", written as `∨` to connect two atomic propositions. Symbolically, we write 
```lean
#check p ∨ q
```
 to check that the compound `p ∨ q` is a proposition.

Students used to digital logic will wonder why we are using ∨ instead of the symbol +. The main reason is that + will usually mean actual addition when things get more complicated. Thus, mathematicans have invented new symbols for logical connectives. Here are the most important for our current purposes: 
```lean
#check ¬p               -- not p
#check p ∨ q            -- p or q
#check p ∧ q            -- p and q
#check p → q            -- p implies q
#check p ↔ q            -- p if and only if q
#check True
#check False
```
 We also have the propositional `False` which denotes **absurdity**. In intuitionistic logic, `¬p` is just shorthand for

```
p → False
```

```lean
#check False
#check p → False
```
 Also note that ↔ is just shorthand for → in both directions
```
p ↔ q  ≡  p → q ∧ q → p
```

## Constructive Proofs

The goal is this chapter is to define a mathematical framework in which we prove statements by constructing proofs. In particular,

- To prove p ∧ q we construct a proof of p and another proof of q.
- To prove p ∨ q we construct a proof of p or we construct a proof of q.
- To prove p → q we supply a method for converting a proof of p into a proof of q
- To prove ¬p (which is p → ⊥) we supply a method to convert a proof of p to ⊥

### Example: A Constructive Proof in Lean 
```lean
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      have hqr : q ∨ r := h.right
      Or.elim hqr
        (λ hq : q => Or.inl (And.intro hp hq))
        (λ hr : r => Or.inr (And.intro hp hr))
    )
    (λ h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (λ hpq : p ∧ q => And.intro hpq.left (Or.inl hpq.right))
        (λ hpr : p ∧ r => And.intro hpr.left (Or.inr hpr.right))
    )
```
 Don't worry if this doesn't make sense right now. It will soon.

## Comparison to Classical Logic

We have defined **intuitionistic** logic or **constructive logic**, different from **classical logic**. In classical logic, the truth of a statement like
```
p ∨ ¬p
```
is guaranteed by the **law of the exluded middle**. You know one of them must be true. In constructive mathematics, you have to either construct a proof of `p` or construct a proof of `¬p`. As an example, consider the proposition:

> The universe is infinite or the universe is finite.

Neither part of this compound proposition currently has a proof. Classically, we would still conclude it is true, but constructively we are just stuck. Similar issues arise with famous mathematical conjectures such as

> P = NP or P ≠ NP

and

> There are either a finite number of twin primes, or an infinite number of twin primes.

These statements may be proved some day, but for now, we cannot conclude they are true using constructive mathematics.

### Double Negation

Similar to the law of the excluded middle is double negation:
```
¬¬p ↔ p
```
Classically, this is a tautology (a proposition that is always true). But constructively, from a proof of "it is not the case that p is not true" one cannot necessarily construct a proof that `p` is true.

As a result, `proof by contradiction` is not valid constructively, because in proof by contradition one follows the procedure:
```
To prove `p`, assume `¬p` and derive `False`.
```
Just because we have a way to transform a proof of `¬p` into `False` does not mean we can have a construction of a proof of `p`.


### Classical Logic

TODO

## Contexts

We now begin to build a framework for proving theorems in propositional logic. The first thing we need is a way to keep track of what propositions we currently know in the course of proving something.

To this end we define a **context** to be a finite set of propositions. Given two contexts `Γ` and `Δ` we can take their union `Γ ∪ Δ` to make a new context. The notation is a bit cumbersome, so we write `Γ,Δ` instead. In particular, if `φ ∈ Φ` then `Γ,φ` is shorthand for `Γ ∪ {φ}`.

If we can show that a proposition `φ` is true whenever all the propositions in a context `Γ` are true, we write
```
Γ ⊢ φ
```
which reads gamma `entails` `φ`. Furthermore, if a proposition `φ` is tautology (meaning it is always true like `p ↔ p`) then it is true independent of any context. That is, the empty context entials any tautology. Thus, we write
```
⊢ φ
```
to mean `∅ ⊢ φ`. We will define precisely what the entails relationship means next.

## Rules of Inference

A **rule of inference** is set of **premises** and a **conclusion** that can be drawn from those premises. The propositional logic we define has only a handful of rules of inference from which all proofs can be constructed. They are presented with a name followed by what looks like a fraction with the premises listed on top and the conslusion on the bottom.
```
                Γ₁ ⊢ A    Γ₂ ⊢ B    Γ₃ ⊢ C
  RULE NAME    ————————————————————————————
                          Γ ⊢ D
```
In this schemantic, the rule has three premises, each of which describe an assumption that a particular context entails a particular proposition. And the rule has one conclusion, stating the entailment you are allowed to conclude. Usually, the contexts listed and the propositions are related in some way. - #

## Axioms

The first rule has no premises and simply states that `φ` can be concluded from any context containing φ. Said constructively, if we have a proof of `φ`, then obviously we can construct a proof of `φ`.
```
  AX  ——————————
       Γ,φ ⊢ φ
```

Here is a simple proof that `{hp:p} ⊢ p` in Lean using the Axiom rule: 
```lean
example (hp : p) : p :=
  hp
```
 If you look at this proof in the infoview, putting your cursor at the beginning of the second like, you will see
```
hp : p
⊢ p
```
Which says, give we have a proof `hp` of `p`, we need show `p`. This is easy, we jsut use `hp` itself.


## Implies Rules

We have two rules for the → connective:
```
              Γ,φ ⊢ ψ
  →-Intro   ————————————
             Γ ⊢ φ → ψ

            Γ ⊢ φ → ψ    Γ ⊢ φ
  →-Elim   —————————————————————
                 Γ ⊢ ψ
```
The **Implies Introduction** rule allows us to introduce `φ → ψ` whenever we have `Γ` and `φ` together entailing `ψ`. The **Implies Elimination** rule is also know as **Modus Ponens**. It states that if we know `φ` implies `ψ` and we know `φ`, then we know `ψ`.

Notice that implies is written with an arrow `→` just like function abstraction in the λ-calculus. This is because one way to think about a proof of `φ→ψ` is to require it to have the form of a function that converts proofs of `φ` into proofs of `ψ`. This suggests that the way to prove statements with implications is to use  λ-calculus expressions. Here are a couple of examples.

First we show and example of →-Intro. The context includes a proof of `p`. Thus we can _introduce_ `q→p` for any `q`. We do this with a lambda expression taking a proof of `q` (and in this case ignoring it) and returning the proof `hp` of `p` available in the context. 
```lean
example {hp : p} : q → p :=
  λ hq => hp
```
 Next, here is an example of →-elim. We have a context with a proof of `p→q` and a proof of `p`. We know the proof `hp` of `p→q` is a lambda abstraction. So we can apply it to a proof `hp` of `p` to get a proof of `q`. 
```lean
example {hpq: p → q} {hp: p} :=
  hpq hp
```
 A complete description of how →-introduction works works is in the chapter on the [Curry-Howard Isomorphism](./CurryHoward.md)

## And Rules

Next we have three rules for the ∧ connective:
```
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

Whenever we see "Intro" that means we are introducing a connective (in this case `∧`) into our conclusion. Whenever we see "Elim" that means we are eliminating part of a compound statement in our conclusion. Here, the **And Introduction** rule shows that we can construct a proof of `φ ∧ ψ` whenever the context contains a proof of `φ` and a proof of `ψ`. The **And Elimination** rules allow us to "eliminate" half of the proposition `φ ∧ ψ` to conclude the weaker statement `φ` or to conclude the weaker statement `ψ`. Said differently, if we have a proof of `φ∧ψ` then we can construct a proof of `φ` by just eliminating the part of the proof of `φ∧ψ` that shows `ψ`.

Unlike the somewhat cryptic rules for implies, the And rules just have functions (like `And.intro`) already defined for them. Here are examples of all of these rules in Lean. 
```lean
#check And.intro
#check And.left
#check And.right

example (hp : p) (hq : q) : p ∧ q :=
  And.intro hp hq

example (hpq : p ∧ q) : p :=
  And.left hpq

example (hpq : p ∧ q) : q :=
  And.right hpq
```
 ## Or Rules

Then we have three rules for the ∨ connective:
```
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

The **Or Introduction** rules allow us to conclude `φ ∨ ψ` from one of its parts. The **Or Elimination** rule looks complicated, but it is straightforward. It says that if we know `Γ ⊢ φ ∨ ψ` then we know that `Γ` must entail either `φ` or `ψ`. If we also know that both `φ` and `ψ` separately entail `ρ`, then we know that `Γ` must entail `ρ`.

Here are examples of the OR rules in Lean. 
```lean
#check Or.inl
#check Or.inr
#check Or.elim

example (hp : p) : p ∨ q :=
  Or.inl hp

example (hq : q) : p ∨ q :=
  Or.inr hq

example (hpq : p ∨ q) : q ∨ p :=
  Or.elim
    hpq
    (λ hp => Or.inr hp)
    (λ hq => Or.inl hq)
```
 ## Ex Falso

Finally, we have the a rule for the ¬ connective:
```
                Γ ⊢ False
  False -Elim ————————————
                  Γ ⊢ φ
```

which states that you can conclude anything if you have a proof of ⊥. This rule is also know as `ex falso sequitur quodlibet` or just `ex falso` or the `principle of explosion`! Here's an example: 
```lean
#check False.elim

example { hf : False } : p :=
  False.elim hf
```
 ## Proofs

A **proof** that `Γ ⊢ φ` is sequence of statements of the form `Γ' ⊢ φ'` each of which is either (a) an axiom or (b) obtained from previous statements in the sequence by one of the inference rules. 
 ### Example 1

As an example, we will prove the statement
```
∅ ⊢ (p∧q)→p
```
Working backwards from this goal, we see that `→-Intro` can be applied to produce this statement where `φ` is `p∧q` and `ψ` is `p`. Thus, we get an instance of →-Intro of the form
```
  p∧q ⊢ p
———————————          (Instantiation of →-Intro)
 ⊢ (p∧q)→p
```
We have now a simpler problem, which is to show `p∧q ⊢ p`. The ∧-Elim-Left rule applies here with `φ=p∧q`, `ψ=p`, and `Γ={p∧q}` giving us the instance
```
  p∧q ⊢ p∧q
——————————————       (Instantiation of ∧-Elim-Left)
   p∧q ⊢ p
```
And now we have an even simpler problem, which is to show that p∧q ⊢ p∧q. But this matches the axiom rule with `Γ={p∧q}` and `φ = p∧q`. Putting all this together into a proof gives us the following:
```
  1) p∧q ⊢ p∧q          axiomatically
  2) p∧q ⊢ p            from (1) via ∧-Elim-Left
  3) ⊢ (p∧q)→p          from (2) via →-Intro
```
And that's it. Our first proof!

Here is the same proof in Lean: 
```lean
example : p∧q → p :=
  λ hpq => And.left hpq
```
 The lambda expression encodes →-Intro, and `And.left` encodes ∧-Left.

What you can take away from this is the idea that constructing this proof is a purely syntactic endeavor. One can easily imagine an algorithm that does this automatically by pattern matching a given sub-goal against the `Γ`, `φ` and `ψ` in the description of a inference rule. The challenge is, of course, as we introduce more expressibility into our logic, and more inference rules, finding the right rules to apply at the right time amounts to a brute force search of all possible inference rules and all possible ways of instantiating those inference rools.

The other thing to notice is that the proof itself looks a lot like a program. In Lean and similar construction-based theorem provers, this observation is made precise. And it will turn out that writing proofs and writing programs amount to the same thing!

### Example 2

Here is a slightly more complicated example. Let's prove
```
⊢ ¬p→(p→q)
```
Recall `¬p` is just shorthand for `p→⊥`. So we're actually trying to prove
```
⊢ (p→⊥)→(p→q)
```
Once again, working backwards, we can apply →-Intro to get
```
p→⊥ ⊢ p→q
```
and then apply →-Intro again to get
```
p→⊥,p ⊢ q
```
Our context now contains both `¬p` and `p`. Using ⊥-elim we get
```
p→⊥,p ⊢ ⊥
```
This subgoal matches the form of →-Elim with `φ=p` and `ψ=⊥`. Using this rule, we get two further subgoals that are just axioms:
```
p→⊥,p ⊢ p→⊥      and      p→⊥,p ⊢ p
```

Putting this all together, we get the following proof:
```
  1) p→⊥,p ⊢ p→⊥        axiomatically
  2) p→⊥,p ⊢ p          axiomatically
  3) p→⊥,p ⊢ ⊥          from (1) and (2) via →-Elim
  4) p→⊥,p ⊢ q          from (3) via ⊥-elim
  5) p→⊥ ⊢ p→q          from (4) via →-Intro
  6) ⊢ (p→⊥)→(p→q)      from (5) via →-Intro
```
And we're done! This is complicated though. Clearly we need a proof assistant to help us! In Lean this proof looks like:  
```lean
theorem t : ¬p→(p→q) :=
  λ hnp => λ hp => False.elim (hnp hp)
```
 ## The Law of the Excluded Middle

As we said, the law of the excluded middle states that

  ⊢ φ ∨ ¬φ

for all propositions φ. However, this statement is not provable using the inference rules above. To prove this meta-mathematical observation is beyond the scope of this lecture and requires an argument about the formal `semantics` of intuitionist propositional logic. For now, accept the fact that φ ∨ ¬φ cannot be proved rom the inference rules given, despite its seeming obviousness.

For this reason, intutionistic logic is weaker than classical logic. However, we can obtain classical logic by adding the above as a new axiom. When we get to proving statements in Lean, we'll see that we can add this axiom into our proofs if we would like to, so it is not big problem. However, it is also remarkable how much of mathematics we can do without this axiom.

## Exercises

1. Prove `∅ ⊢ p → (p ∨ q)`
1. Prove `∅ ⊢ (p ∨ q) → (q ∨ p)`


 # REFERENCES

Morten Heine Sørensen, Pawel Urzyczyn
"Lectures on the Curry-Howard Isomorphism"
Elsevier. 1st Edition, Volume 149 - July 4, 2006.
  - Chapter 2 describes Intuitionistic Propositional Logic



<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
