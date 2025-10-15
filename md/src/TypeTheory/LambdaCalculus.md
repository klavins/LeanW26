

Background
===

The **λ-calculus** was introduced in the 1930s by Alonzo Church as a way to represent how functions on natural numbers are calculated using symbols. The goal was to determine whether every function on the natural numbers had an effective means of being calculated.

Said differently, the question is: Does every function have an algorithm? Astonishingly, Church showed that the answer is "no". In fact, there are functions on the natural numbers for which there is no effective algorithm. Church's 1935 paper "An unsolvable problem in elementary number theory" proved this result.

The reasoning, roughly, is this:

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


```lean
def f := λ x ↦ x+1

#print f
#reduce f

def g := λ x ↦ λ y ↦ 2*x-y

#reduce g 2
#reduce g 2 3
```
 Note: The Lean Powers have recently decreed that λ and ↦ should be written as fun and =>.
So, we'll use syntax like: 
```lean
def f' := fun x => x+1
def g' := fun x y => 2*x-y
```

Exercise
===

Define a lambda called `h` that returns the square of its argument.
Then evaluate `h (h (h 2))`.




Unsolvable Problems
===

A specific problem that Church showed to be unsolvable is:

> Given λ-calculus terms M and N, show there does not exist a λ-calculus function that can determine whether M can be rewritten as N.

Those who have studied theoretical computer science, may be familiar with Alan Turing's similar result which shows there is no Turing Machine that can determine whether a given Turing Machine eventually terminates. In fact, the λ-calculus can simulate Turing Machines and vice verse.

The Church-Turing Thesis is the observation that _all_ formalizations of computation are in fact equivalent to the λ-calculus or, equivalently, Turing Machines. The former is more convenient for symbolic reasoning, while the latter is more akin to how electromechanical computers actually work.

Programming Languages
===

Thus, the λ-calclus and the formal notion of computation has its roots in the foundations of mathematics. Later, around the 1960s, linguists and computer scientists realized that the λ-calculus was an useful framework for the theory and design of programming languages.

Simultaenously, logicians were becoming frustrated with Set Theory as a foundation for mathematics and started exploring Type Theory as an alternative. Around the 1990s many of these ideas came together, especially through the work of Thierry Coquand on the Calculus of Constructions. It was observed that typed programming languages were not only an ideal foundation for all of mathematics, they could be used to develop computational proof assistants and theoerm provers.

Infinite Loops
===
Define the term
```
Ω := λ x => x x
```
and consider `Ω` applied to itself `Ω`:
```
(λ x => x x) (λ x => x x)       —β—>       (λ x => x x) (λ x => x x)
```
producing an infinite loop.

Curry's Paradox
===

Infinite Loops made the λ-calculus expressive enough for Church to prove his undecidability results, but it caused other problems when logicians wished to use formalisms like the λ-calculus as systems of logic.

Haskel Curry discovered that one could encode the following paradox:

  - Consider the self-referential statement X = X → Y where Y is _any_ statement.
  - Certainly X → X is true for any statement X.
  - Substituting X → Y for the second X gives X → (X → Y)
  - This statement is equivalent to X → Y, which is the same as X
  - Thus X is true
  - So Y is true since X → Y

For example, X → Y could mean "If this sentence is true, then 1 > 0." Any framework in which you can make this argument allows you to prove any statement Y, and so the framework is useless logically.

Types
===

The solution was to assign _types_ to all terms in the λ-calculus. We will see that certain self referential programs are impossible to assign types to. At the same time, infinite loops are no longer allowed, making the formalism not as powerful from a computational point of view.

Thus was born the _simply-typed λ-calculus_. Eventually, more complicated types were added, in which type definitions could depend on other types or on even terms. Most modern programming languages and some logical frameworks have these properties.

Church's paper on the subject is quite complicated, elucidating ideas that were fairly novel at the time. Since then, comptuer scientists have refined the ideas into a very simple framework, which is presented here, and which can be found in numerous textbooks.

Church is my great, great grand co-advisor (Church > Scott > Rounds > Klavins).


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

