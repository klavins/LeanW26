
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

<div class="lean-code" data-start-line="79" data-end-line="80"><pre><code>variable (f : Nat → Nat)
#check ∀ x : Nat , ∃ y : Nat , f x &gt; y</code></pre></div>


Objects
===

**Objects** in FOL can come from any agreed upon universe.
Since we will be using Lean to work with first order logic,
you can just assume that objects are any basic terms: numbers,
strings, lists, and so on.

In what follows, we'll use a simple type with four values. 

<div class="lean-code" data-start-line="94" data-end-line="98"><pre><code>inductive Person where | mary | steve | ed | jolin

open Person

#check ed                    -- Person</code></pre></div>


Predicates
===

A **predicate** is a `Prop` valued function.

For example, a predicate on `Person` is a function from `Person` into `Prop`.

For example, 

<div class="lean-code" data-start-line="112" data-end-line="116"><pre><code>def InSeattle (x : Person) : Prop := match x with
  | mary  | ed    =&gt; True
  | steve | jolin =&gt; False

#check InSeattle</code></pre></div>

 Predicates can be used with connectives to make compound propositions. 

<div class="lean-code" data-start-line="120" data-end-line="121"><pre><code>example : InSeattle steve ∨ ¬InSeattle steve :=
  Or.inr id</code></pre></div>


Example: A Predicate on ℕ
===

Or we might define a predicate inductively on the natural numbers. 

<div class="lean-code" data-start-line="129" data-end-line="139"><pre><code>def is_zero (n : Nat) : Prop := match n with
  | Nat.zero =&gt; True
  | Nat.succ _ =&gt; False

#check is_zero

example : ¬is_zero 91 :=              -- is_zero 91 → False
  id

example : is_zero 0 :=                -- True (definitionally)
  trivial</code></pre></div>


Predicates with Multiple Arguments
===

We may define predicates to take any number or arguments, including no arguments at all. 
 No-argument predicates are just normal propositions 

<div class="lean-code" data-start-line="149" data-end-line="150"><pre><code>variable (P : Prop)
#check P</code></pre></div>

 A one-argument predicate 

<div class="lean-code" data-start-line="154" data-end-line="155"><pre><code>variable (InWashington : Person → Prop)
#check InWashington steve</code></pre></div>

 A two-argument predicate 

<div class="lean-code" data-start-line="159" data-end-line="160"><pre><code>variable (Age : Person → Nat → Prop)
#check Age jolin 27</code></pre></div>


Relations
===

A two-argument predicate is called a **relation**.

For example, we might define a predicate on pairs of people such as 

<div class="lean-code" data-start-line="170" data-end-line="174"><pre><code>def on_right (p q : Person) : Prop := match p with
  | mary =&gt; q = steve
  | steve =&gt; q = ed
  | ed =&gt; q = jolin
  | jolin =&gt; q = mary</code></pre></div>

 We can define other predicates in terms of existing predicates. 

<div class="lean-code" data-start-line="178" data-end-line="181"><pre><code>def next_to (p q : Person) := on_right p q ∨ on_right q p

example : next_to mary steve :=
  Or.inl (Eq.refl steve)</code></pre></div>


Greater Than is a Relation
===

 Relations are often represented with *infix* notation, but they are still just
predicates. For example, in Lean, the greater-than relation on natural numbers is: 

<div class="lean-code" data-start-line="191" data-end-line="192"><pre><code>#check @GT.gt Nat
#eval GT.gt 2 3</code></pre></div>

 This doesn't look very nice, so Lean defines notation:

```lean
infix:50 " > "  => GT.gt
```
and we can write: 

<div class="lean-code" data-start-line="201" data-end-line="201"><pre><code>#eval 2 &gt; 3</code></pre></div>

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

<div class="lean-code" data-start-line="242" data-end-line="248"><pre><code>example : ∀ (x : Person) , (InSeattle x) ∨ ¬(InSeattle x) :=
  fun x =&gt;
  match x with
  | steve =&gt; Or.inr id
  | mary =&gt; sorry
  | ed =&gt; sorry
  | jolin =&gt; sorry</code></pre></div>


Classical reasoning is not required `InSeattle` explicitly lists all cases,
providing a constructive proof of each one.


∀ is Syntactic Sugar
===

`∀` is just syntactic sugar for polymorphism. The above FOL statement
can be equally well written as: 

<div class="lean-code" data-start-line="262" data-end-line="262"><pre><code>#check (x : Person) → (InSeattle x) ∨ ¬(InSeattle x)</code></pre></div>

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

<div class="lean-code" data-start-line="307" data-end-line="310"><pre><code>variable (α : Type) (P Q : α → Prop)

example : (∀ x, P x ∧ Q x) → ∀ y, P y :=
  fun h y =&gt; (h y).left</code></pre></div>


Exercise
===

<ex /> Show the following using a term level proof and without using Lean's library of theorems.



<div class="lean-code" data-start-line="320" data-end-line="320"><pre><code>example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := sorry</code></pre></div>


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

<div class="lean-code" data-start-line="366" data-end-line="366"><pre><code>#check ∃ x, P x</code></pre></div>

 for 

<div class="lean-code" data-start-line="370" data-end-line="370"><pre><code>#check Exists (fun x =&gt; P x)</code></pre></div>


Using Exists-intro
===

All we need to introduce an existentially quantified statement with predicate `P`
is an element and a proof that `P` holds for that element.

An example use of the introduction rule is the following.
The assumption that `α has at least one element q` is necessary.  

<div class="lean-code" data-start-line="383" data-end-line="384"><pre><code>example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  fun hp =&gt; Exists.intro q (hp q)</code></pre></div>

 Or more concisely, 

<div class="lean-code" data-start-line="388" data-end-line="389"><pre><code>example (q : α) : (∀ x , P x) → (∃ x , P x) :=
  fun hp =&gt; ⟨ q, hp q ⟩</code></pre></div>


Exercise
===

<ex /> Prove the following



<div class="lean-code" data-start-line="399" data-end-line="400"><pre><code>example : ∃ x, on_right mary x := sorry
example : ∃ x, ¬on_right mary x := sorry</code></pre></div>


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

<div class="lean-code" data-start-line="441" data-end-line="443"><pre><code>example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  sorry                                      -- ⊢  ∀ (a : α), P a ∧ Q a → ∃ x, Q x ∧ P x</code></pre></div>

 

<div class="lean-code" data-start-line="447" data-end-line="449"><pre><code>example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  (fun c ⟨ hq, hp ⟩ =&gt; sorry)                -- ⊢ ∃ x, Q x ∧ P x</code></pre></div>

 

<div class="lean-code" data-start-line="453" data-end-line="455"><pre><code>example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  (fun c ⟨ hq, hp ⟩ =&gt; ⟨ c, sorry ⟩)         -- ⊢  c ∧ P c</code></pre></div>

 

<div class="lean-code" data-start-line="459" data-end-line="461"><pre><code>example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  Exists.elim h
  (fun c ⟨ hq, hp ⟩ =&gt; ⟨ c, ⟨ hp, hq ⟩ ⟩ )</code></pre></div>


Example Proofs
===


<div class="lean-code" data-start-line="468" data-end-line="468"><pre><code>variable (p : Type → Prop) (r : Prop)</code></pre></div>

 You can use pattern matching and brackets to do proof-golfing 

<div class="lean-code" data-start-line="471" data-end-line="473"><pre><code>example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := ⟨
    (fun ⟨ c, ⟨ hc, hr ⟩ ⟩ =&gt; ⟨ ⟨ c, hc ⟩, hr ⟩ ),
    (fun ⟨ ⟨ c, hc ⟩, hr ⟩ =&gt; ⟨ c, ⟨ hc, hr ⟩ ⟩ ) ⟩</code></pre></div>

 But sometimes it is easier to read if you do not: 

<div class="lean-code" data-start-line="477" data-end-line="480"><pre><code>example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h x hp =&gt; h (Exists.intro x hp))
  (fun h he =&gt; Exists.elim he (fun y hy =&gt; h y hy))</code></pre></div>

 Here is an example using `Person`: 

<div class="lean-code" data-start-line="484" data-end-line="487"><pre><code>example : ∀ (x : Person) , (InSeattle x) ∨ ¬(InSeattle x) :=
  fun x =&gt; match x with
    | mary  | ed    =&gt; Or.inl trivial
    | steve | jolin =&gt; Or.inr (fun h =&gt; False.elim h)</code></pre></div>


Intermediate Results
===

The keyword `have` is like `let`, except for `Prop`. You can use it to
define intermediate results.


<div class="lean-code" data-start-line="498" data-end-line="505"><pre><code>example (h₁ : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=

  have h₂ : ∀ w, P w ∧ Q w → ∃ x, Q x ∧ P x :=
            fun w =&gt;
            fun hpq : P w ∧ Q w  =&gt;
            ⟨ w, ⟨ hpq.right, hpq.left ⟩ ⟩

  Exists.elim h₁ h₂</code></pre></div>


Exercises
===

<ex /> Prove the following FOL examples using introduction, elimination, etc.
using term level proofs (and withouth using library theorems).



<div class="lean-code" data-start-line="517" data-end-line="529"><pre><code>--hide
variable (p q : Type → Prop)
variable (r : Prop)
--unhide

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun h1 h2 =&gt;
    match h2 with
    | Exists.intro c hc =&gt; h1 c hc)
  sorry

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=  sorry</code></pre></div>


<ex /> Given the definitions of `Person`, `on_right`, and `next_to`:

Prove the following examples: 

<div class="lean-code" data-start-line="536" data-end-line="538"><pre><code>example : ∀ p q , on_right p q → next_to p q := sorry
example : ∀ p : Person, ∃ q : Person, next_to p q := sorry
example : ∀ p : Person, ∃ q : Person, ¬next_to p q := sorry</code></pre></div>


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

<div class="lean-code" data-start-line="557" data-end-line="558"><pre><code>inductive Exists1 {α : Type} (p : α → Prop) : Prop where
  | intro (x : α) (h : p x ∧ ∀ y : α, p y → x = y) : Exists1 p</code></pre></div>

 However, it is a pain to define the notation `E!`. So we will just have to write

```lean
Exists1 (fun x => P x)
```

instead of the above.

Exercises
===

<ex /> Prove the elimination theorem for `Exists1`



<div class="lean-code" data-start-line="575" data-end-line="576"><pre><code>theorem Exists1.elim {α : Type} {P : α → Prop} {b : Prop}
   (h₁ : Exists1 (fun x =&gt; P x)) (h₂ : ∀ (a : α), P a → b) : b := sorry</code></pre></div>


<ex /> Prove the following examples:


<div class="lean-code" data-start-line="582" data-end-line="589"><pre><code>example : ∀ x, Exists1 (fun y : Person =&gt; x ≠ y ∧ ¬next_to y x ) := sorry
example (α : Type) (P : α → Prop) : Exists1 ( fun x =&gt; P x ) → ¬ ∀ x, ¬ P x  := sorry
example : Exists1 (fun x =&gt; x=0) := sorry
example : ¬Exists1 (fun x =&gt; x ≠ 0) := sorry

--hide
end LeanW26
--unhide</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

