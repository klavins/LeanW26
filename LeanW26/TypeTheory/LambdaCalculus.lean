import Mathlib

/-

Background
===

The **λ-calculus** was introduced in the 1930s by Alonzo Church as a way to represent
how functions on natural numbers are calculated using symbols.

Church asked: Does every function have an algorithm?

Church showed that the answer is "no". The reasoning, roughly, is this:

  - Devise a simple programming language, the λ-calculus
  - Define computation as rewriting operations on λ-calculus terms
  - Correspond to every term a natural number
  - Conclude that questions about terms are thus questions about numbers
  - Show there are more functions from terms into terms than there are terms.

The λ-Calculus
===

Specifically, the λ-calculus has two parts:

**Term Syntax**
- Variables: `x, y, z, ...` are terms
- Abstraction: If `x` is a variable and `M` is a term then `λ x ↦ M` is a term
- Application: If `M` and `N` are terms, then `M N` is a term

**β-Reduction**
- `λ x ↦ M` applied to `N` is `M[N/x]`, where all occurances of x are replaced with N.

The λ-Calculus in Lean
===

In Lean you can write lambda calculus statements and reduce them, for example:

-/

def f1 := λ x ↦ x+1
def g1 := λ x ↦ λ y ↦ 2*x-y

#reduce f1 2         -- 3
#reduce g1 2 3       -- 1

/- Note: The Lean Powers have recently decreed that `λ` and `↦` should be written as `fun` and `=>`.
So, we'll use syntax like: -/

def f2 := fun x => x+1
def g2 := fun x y => 2*x-y

/-
Exercises
===

<ex/> Define a lambda called `h` that returns the square of its argument.

<ex/> Evaluate `h (h (h 2))`.

-/

/-

Unsolvable Problems
===

A specific problem that Church showed to be unsolvable is:

> Given λ-calculus terms M and N, show there does not exist a λ-calculus function
that can determine whether M can be rewritten as N.

This argument is similar to Alan Turing's similar result which shows there is no
Turing Machine that can determine whether a given Turing Machine eventually terminates.

The *Church-Turing Thesis* is the observation that _all_ formalizations of
computation are equivalent to the λ-calculus or, equivalently, Turing Machines.

The former is more convenient for symbolic reasoning, while the latter is more
akin to how electromechanical computers actually work.

Programming Languages
===

Thus, the λ-calclus and the formal notion of computation has its roots in the
foundations of mathematics.

In the 1960s, linguists and computer scientists realized that the λ-calculus
was an useful framework for the theory and design of programming languages.

Simultaenously, logicians were becoming frustrated with Set Theory as a foundation
for mathematics and started exploring Type Theory as an alternative. In 1990s many
of these ideas came together, especially through the work of Thierry Coquand on
the *Calculus of Constructions*.

It was observed that typed programming languages were not only an ideal foundation
for all of mathematics, they could be used to develop computational proof assistants
and theoerm provers.


Infinite Loops
===

Central to Church's (and Turing's) argument is that some evaluations go on infinitely,
some do not, and it is not always easy to tell the difference.

Here is an easy example of infinite behavior. Define
```
Ω := λ x => x x
```
Consider `Ω` applied to itself `Ω`:
```
(λ x => x x) (λ x => x x)       —β—>       (λ x => x x) (λ x => x x)
```
producing an infinite loop.

Exercises
===

<ex/> Define `Ω` in Lean and explain what happens.


Curry's Paradox
===

Infinite Loops made the λ-calculus expressive enough for Church
to prove his undecidability results, but it caused other problems.

Haskel Curry discovered that one could encode the following paradox in logical
systems built from the λ-calculus.

  - Suppose X = X → Y where Y is _any_ statement.
  - Certainly X → X is true for any statement X.
  - Substituting X → Y for the second X gives X → (X → Y)
  - This statement is equivalent to X → Y, which is X by assumption.
  - Thus X is true
  - So Y is true since X → Y

For example, X → Y could mean "If this sentence is true, then 1 < 0."

Types
===

The solution was to assign _types_ to all terms in the λ-calculus.
- Self referential programs are impossible to assign types to.
- Infinite loops are no longer allowed (less powerful computationally).

Thus was born the _simply-typed λ-calculus_.

Eventually, more complicated types were added, in which type definitions could
depend on other types or on even terms.

Most modern programming languages and some logical frameworks have these properties.

The Simply-Typed Lambda Calculus
===

In the expressions we wrote above, the types were inferred, but we can write them out.
-/

def f3 : Nat → Nat := fun (x : Nat) => x+1
def g3 : Nat → Nat → Nat := fun (x y : Nat) => 2*x-y

/-
However, `Nat` is not a *simple* type (it is an *inductive* type).

An example of simply typed expression is:
-/

def f4 : fun (h: Type → Type → Type) => fun (x : Type) h x x

/-
In the next section we'll look at what exactly is `Type` and come back to
the lambda calculus in the following section.
-/
