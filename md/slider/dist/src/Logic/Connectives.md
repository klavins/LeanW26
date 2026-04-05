
Propositional Connectives
===

Overview
===
Inductive types capture all of propositional logic, first order logic, and more.

Instead of defining _and_, _or_ and the other logical connectives as
built-in operators in CIC, they are just defined terms of more primitive inductive types.

In this slide deck we redefine the connectives, to understand how they work.
To avoid naming conflicts with Lean's standard library, we open a namespace.


<div class="lean-code" data-start-line="27" data-end-line="27"><pre><code>namespace Temp</code></pre></div>

 And we define some variables to use throughout. 

<div class="lean-code" data-start-line="31" data-end-line="31"><pre><code>variable (p q r : Prop)</code></pre></div>

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

<div class="lean-code" data-start-line="51" data-end-line="51"><pre><code>example (hp : p) : p :=  hp</code></pre></div>

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



<div class="lean-code" data-start-line="73" data-end-line="77"><pre><code>def prop_id (hp : p) := hp

theorem prop_id_thm (hp : p) : p := hp

example (hp : p) : p := hp</code></pre></div>

 Also, `prop_id` is really just a special case of the identity function. 

<div class="lean-code" data-start-line="81" data-end-line="83"><pre><code>def my_id.{u} {α : Sort u} (x : α) : α := x

example (hp : p) : p := my_id hp</code></pre></div>

 Finally, example is not just for `Prop`: 

<div class="lean-code" data-start-line="87" data-end-line="87"><pre><code>example : Nat := 10000001</code></pre></div>


Implication in Lean
===

**`→-Intro` is lambda abstraction:** Whenever you see a goal of the form `A → B`, you
write a lambda to get a simpler goal.


<div class="lean-code" data-start-line="97" data-end-line="101"><pre><code>example (hp : p) : q → p :=
  fun hq =&gt; sorry                           -- goal for the `sorry` is `p`

example (hp : p) : q → p :=
  fun hq =&gt; hp</code></pre></div>


**`→-Elim` is lambda application:** When you see function (with type `A → B`) in a context
you can apply it to get a simpler goal.


<div class="lean-code" data-start-line="108" data-end-line="112"><pre><code>example (hpq : p → q) (hp : p) : q :=
  hpq sorry                                 -- goal for the `sorry` is `p`

example (hpq : p → q) (hp : p) : q :=
  hpq hp</code></pre></div>


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

<div class="lean-code" data-start-line="131" data-end-line="132"><pre><code>inductive And (p q : Prop) : Prop where
  | intro : p → q → And p q</code></pre></div>

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


<div class="lean-code" data-start-line="163" data-end-line="164"><pre><code>example : q → p → And p q :=
  fun hq =&gt; fun hp =&gt; And.intro hp hq</code></pre></div>


And Elimination
===

The elimination rules for `And` are
```none
                Γ ⊢ p ∧ q                          Γ ⊢ p ∧ q
  ∧-Elim-Left ——————————————         ∧-Elim-Right —————————————
                  Γ ⊢ p                              Γ ⊢ q
```
which we can write in Lean as 

<div class="lean-code" data-start-line="179" data-end-line="185"><pre><code>def And.left {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro hp _ =&gt; hp

def And.right {p q : Prop} (hpq : And p q) :=
  match hpq with
  | And.intro _ hq =&gt; hq</code></pre></div>


Proofs with And-Elimination
===

With these inference rules, we can do more proofs: 

<div class="lean-code" data-start-line="193" data-end-line="194"><pre><code>example : (And p q) → (And q p) :=
  fun hpq =&gt; And.intro hpq.right hpq.left</code></pre></div>


Match is Enough
===

The elimination rules above are a _convenience_ we defined to make the proof look
more like propositional logic. We could also have written: 

<div class="lean-code" data-start-line="206" data-end-line="209"><pre><code>example (p q : Prop) : (And p q) → p :=
  fun hpq =&gt;
  match hpq with
  | And.intro hp _ =&gt; hp</code></pre></div>

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



<div class="lean-code" data-start-line="232" data-end-line="238"><pre><code>--hide
end Temp -- stop using our temporary namespace and use Lean&#x27;s And
variable (p q r : Prop)
--unhide


#check p ∧ q                        --p ∧ q : Prop</code></pre></div>


Structures
===
With Lean's `And` defined as a structure we can do


<div class="lean-code" data-start-line="246" data-end-line="253"><pre><code>example : (p ∧ q) → (q ∧ p) :=
  fun hpq =&gt; And.intro hpq.right hpq.left

example : (p ∧ q) → (q ∧ p) :=
  fun hpq =&gt; { left := hpq.right, right :=  hpq.left }

example : (p ∧ q) → (q ∧ p) :=
  fun hpq =&gt; ⟨ hpq.right, hpq.left ⟩</code></pre></div>

 You can match the the parts of a structure in the argument to `fun`: 

<div class="lean-code" data-start-line="257" data-end-line="258"><pre><code>example : (p ∧ q) → (q ∧ p) :=
  fun ⟨ hp, hq ⟩ =&gt; ⟨ hq, hp ⟩</code></pre></div>


Exercise
===

<ex /> Show the following using a term level proof without using the library.



<div class="lean-code" data-start-line="270" data-end-line="274"><pre><code>example : p ∧ (q ∧ r) → (p ∧ q) ∧ r := sorry

--hide
namespace Temp
--unhide</code></pre></div>


Or is Inductive
===

To introduce new `Or` propositions, we use the two introduction rules
```none
                 Γ ⊢ p                              Γ ⊢ p
 ∨-Intro-Left ———————————          ∨-Intro-Right ————————————
               Γ ⊢ p ∨ q                          Γ ⊢ p ∨ q
```
In Lean, we have 

<div class="lean-code" data-start-line="288" data-end-line="290"><pre><code>inductive Or (p q : Prop) : Prop where
  | inl (h : p) : Or p q
  | inr (h : q) : Or p q</code></pre></div>

 For example,  

<div class="lean-code" data-start-line="294" data-end-line="295"><pre><code>example : And p q → Or p q :=
  fun ⟨ _, hq ⟩ =&gt; Or.inr hq</code></pre></div>


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

<div class="lean-code" data-start-line="312" data-end-line="315"><pre><code>def Or.elim {p q r : Prop} (hpq : Or p q) (hpr : p → r) (hqr : q → r) :=
  match hpq with
  | Or.inl hp =&gt; hpr hp
  | Or.inr hq =&gt; hqr hq</code></pre></div>


Example of and Or-Elim Proof
===

Here is an example proof using or introduction and elimination. 

<div class="lean-code" data-start-line="323" data-end-line="327"><pre><code>example : Or p q → Or q p :=
  fun hpq =&gt; Or.elim
      hpq                                 -- ⊢ p ∨ q
      (fun hp =&gt; Or.inr hp)               -- ⊢ p → (q ∨ p)
      (fun hq =&gt; Or.inl hq)               -- ⊢ q → (q ∨ p)</code></pre></div>

 Once again, the elimination rule is just a convenience.
The proof could have been written with `match`. 

<div class="lean-code" data-start-line="332" data-end-line="336"><pre><code>example : Or p q → Or q p :=
  fun hpq =&gt;
  match hpq with
  | .inl hp =&gt; Or.inr hp
  | .inr hq =&gt; Or.inl hq</code></pre></div>


True is Inductive
===
`True` is defined inductively as
```lean
inductive True : Prop where
  | intro : True
```

for example:



<div class="lean-code" data-start-line="351" data-end-line="351"><pre><code>example : Or True True := Or.inl True.intro</code></pre></div>

 Or, using Lean's notation and definitons 

<div class="lean-code" data-start-line="356" data-end-line="366"><pre><code>--hide
end Temp
--unhide

#print trivial                 -- theorem trivial : True := True.intro

example : True ∨ True := Or.inl trivial

--hide
namespace Temp
--unhide</code></pre></div>


False is Inductive
===

Finally, we have `False`, which has no introduction rule, kind of like `Empty`,
except we add the requirement that `False` is also type of `Prop`.  

<div class="lean-code" data-start-line="375" data-end-line="375"><pre><code>inductive False : Prop</code></pre></div>

 From `False` we get the `Not` connective, which is *syntactic sugar*. 

<div class="lean-code" data-start-line="379" data-end-line="379"><pre><code>def Not (p : Prop) : Prop := p → False</code></pre></div>

 Here is an example proof: 

<div class="lean-code" data-start-line="383" data-end-line="386"><pre><code>example : (p → q) → (Not q → Not p) :=
  fun hpq hq =&gt;
  fun hp =&gt;
  hq (hpq hp)</code></pre></div>


False Elimination
===

To define the elimination rule for `False`
```
           Γ ⊢ ⊥
  ⊥-Elim ——————————
           Γ ⊢ p
```
we take advantage of the fact that `False` was defined inductively. 

<div class="lean-code" data-start-line="400" data-end-line="401"><pre><code>def False.elim {p : Prop} (h : False) : p :=
  nomatch h</code></pre></div>

 Here is an example proof that from False you can conclude anything: 

<div class="lean-code" data-start-line="405" data-end-line="406"><pre><code>example (p q : Prop) : And p (Not p) → q :=
  fun ⟨ hp, hq ⟩ =&gt; False.elim (hq hp)</code></pre></div>

 This elimination rule provides another way to prove the example: 

<div class="lean-code" data-start-line="410" data-end-line="411"><pre><code>example : False → True :=
  False.elim</code></pre></div>


If and only iff
===

If and only if is defined inductively as
```lean
structure Iff (p q : Prop) : Prop where
  intro ::
  mp : p → q
  mpr : q → p
```

with notation `p ↔ q`.

For example:



<div class="lean-code" data-start-line="434" data-end-line="434"><pre><code>example : p ↔ p := Iff.intro id id</code></pre></div>

 or 

<div class="lean-code" data-start-line="438" data-end-line="438"><pre><code>example : p ↔ p := { mp := id, mpr := id }</code></pre></div>

 or 

<div class="lean-code" data-start-line="442" data-end-line="442"><pre><code>example : p ↔ p := ⟨ id, id ⟩</code></pre></div>


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

<div class="lean-code" data-start-line="469" data-end-line="474"><pre><code>--hide
end Temp -- start using Lean&#x27;s propositions
--unhide

example (p q : Prop) : (p ∧ (¬p)) → q :=
  fun ⟨ hp, hnp ⟩ =&gt; False.elim (hnp hp)</code></pre></div>


<div class='fn'>
  <a href="https://github.com/leanprover/lean4/blob/master/src/Init/Notation.lean">
  Lean's core notation</a></div>



Exercise
===

<ex /> Show



<div class="lean-code" data-start-line="494" data-end-line="494"><pre><code>example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := sorry</code></pre></div>


<ex /> Do all these proofs, which are borrowed from the [Theorem Proving in Lean Book](https://lean-lang.org/theorem_proving_in_lean4/title_page.html). Use only term level proofs. No tactics.


 

<div class="lean-code" data-start-line="502" data-end-line="508"><pre><code>example : p ∨ q ↔ q ∨ p := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬(p ∧ ¬p) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry</code></pre></div>


<ex /> This one requires the law of the excluded middle, which can be
used with `Classical.em`. The way to do this one is to do Or-elimination
on `Classical.em p`.


<div class="lean-code" data-start-line="516" data-end-line="516"><pre><code>example : (p → q) → (¬p ∨ q) := sorry</code></pre></div>


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



<div class="lean-code" data-start-line="538" data-end-line="542"><pre><code>inductive Nor (p q : Prop) : Prop where
  | intro : ¬p → ¬q → Nor p q

def Nor.elim_left {p q : Prop} (hnpq : Nor p q) : Prop := sorry
def Nor.elim_right {p q : Prop} (hnpq : Nor p q) : Prop := sorry</code></pre></div>


Exercise
===

<ex /> Use your `Nor` inference rules, and the regular inference rules from Lean's
propopsitional logic, to prove the following examples.




<div class="lean-code" data-start-line="554" data-end-line="556"><pre><code>example : ¬p → (Nor p p) := sorry
example : (Nor p q) → ¬(p ∨ q) := sorry
example : ¬(p ∨ q) → (Nor p q) := sorry</code></pre></div>


References
===

- Section 7.3 of [TPL](https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html) describes how to define the propositional connectives.



<div class="lean-code" data-start-line="566" data-end-line="568"><pre><code>--hide
end LeanW26
--unhide</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

