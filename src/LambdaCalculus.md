
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/LambdaCalculus.lean'>Code</a> for this chapter</span>
 # The Simply Typed λ-Lambda Calculus

## Background

The **λ-calculus** was introduced in the 1930s by Alonzo Church as a way to represent how functions on natural numbers are calculated using symbols. The goal was to determine whether every function on the natural numbers had an effective means of being calculated.

Said differently, the question is: Does every function have an algorithm? Astonishingly, Church showed that the answer is "no". In fact, there are functions on the natural numbers for which there is no effective algorithm. Church's 1935 paper "An unsolvable problem in elementary number theory" proved this result.

The reasoning, roughly, is this:

  - Devise a simple programming language, the λ-calculus
  - Define computation as rewriting operations on λ-calculus terms
  - Correspond to every term a natural number
  - Conclude that questions about terms are thus questions about numbers
  - Show there are more functions from terms into terms than there are terms.

A specific problem that Church showed to be unsolvable is: Given λ-calculus terms M and N, show there does not exist a λ-calculus function that can determine whether M can be rewritten as N. Those who have studied theoretical computer science, may be familiar with Alan Turing's similar result which shows there is no Turing Machine that can determine whether a given Turing Machine eventually terminates. In fact, the λ-calculus can simulate Turing Machines and vice verse.

The Church-Turing Thesis is the observation that _all_ formalizations of computation are in fact equivalent to the λ-calculus or, equivalently, Turing Machines. The former is more convenient for symbolic reasoning, while the latter is more akin to how electromechanical computers actually work.

## Programming Languages

Thus, the λ-calclus and the formal notion of computation has its roots in the foundations of mathematics. Later, around the 1960s, linguists and computer scientists realized that the λ-calculus was an useful framework for the theory and design of programming languages.

Simultaenously, logicians were becoming frustrated with Set Theory as a foundation for mathematics and started exploring Type Theory as an alternative. Around the 1990s many of these ideas came together, especially through the work of Thierry Coquand on the Calculus of Constructions. It was observed that typed programming languages were not only an ideal foundation for all of mathematics, they could be used to develop computational proof assistants and theoerm provers.

## Curry's Paradox

The original formulation of the λ-calculus allowed for infinite loops, as do most programming languages. This made the λ-calculus expressive enough for Church to prove his undecidability results, but it caused other problems when logicians wished to use formalisms like the λ-calculus as systems of logic.

Haskel Curry discovered that one could encode the following paradox:

  - Consider the self-referential statement X = X → Y where Y is _any_ statement.
  - Certainly X → X is true for any statement X.
  - Substituting X → Y for the second X gives X → (X → Y)
  - This statement is equivalent to X → Y, which is the same as X
  - Thus X is true
  - So Y is true since X → Y

For example, X → Y could mean "If this sentence is true, then 1 > 0." Any framework in which you can make this argument allows you to prove any statement Y, and so the framework is useless logically.

## Types

The solution was to give _types_ to all terms in the λ-calculus. We will see below that certain self referential programs are impossible to assign types to. At the same time, infinite loops are no longer allowed, making the formalism not as powerful from a computational point of view.

Thus was born the _simply-typed λ-calculus_. Eventually, more complicated types were added, in which type definitions could depend on other types or on even terms. Most modern programming languages and some logical frameworks have these properties.

Church's paper on the subject is quite complicated, elucidating ideas that were fairly novel at the time. Since then, comptuer scientists have refined the ideas into a very simple framework, which is presented here, and which can be found in numerous textbooks. The notes in the first part of this section follow video lectures by students of Prof. Uwe Nestmann at the Technical University of Berlin, except that I have restated the formulas in Lean. A link to the videos can be found in the references at the end of this chapter. A Google search will yield hundreds of similar lectures, notes, books, and papers.

### Basic Types

The `simply typed λ-calculus` is an extremely simple programming language that nevertheless captures the essence of computation. It uses type expressions and terms that have those types. We start with the types. First, we assume a base type. In Lean the base type is called `Type`. You can ask lean what `Type` is using the `#check` directive (which stands for "Type Check"). 
```lean
#check Type
```
 Lean tells you `Type` has `Type 1`, which is a synonym for `Type`. Don't worry about this right now and just accept that `Type` is a type. One constructs new types using the arrow `→` as in the following examples: 
```lean
#check Type → Type
#check Type → (Type → Type)
#check (Type → Type) → Type
```
 That is, whenevever τ is a type, so is τ → τ. Arrow types are supposed to denote function types. So τ → τ is the type of any function that takes objects in τ and returns objects in τ. Note that the arrow → associates to the right. So the second expression above is equivalent to `Type → Type → Type`.

### Type Variables and Applications

You can also define type variables using `def` 
```lean
def A := Type
def B := Type → Type
```
 Which looks a bit more like what you would see in a textbook on type theory. Now you can construct more types. 
```lean
#check A → B
```
 ## Terms

Next, we define the terms of the lambda calculus. These are the programs. We start with **variables**, for example `x` and `f`, which we declare in Lean as follows: 
```lean
variable (x : A)               -- declare a variable x of type a
variable (f : A → A)           -- declare a function f from A into A

#check x
#check f
```
 What we've said here is that `x` is a simple object with type `A`, while `f` is an function type from `A` into `A`. Next we have **applications**. These have the form `e₁ e₁` where `e₁` and `e₂` are terms. For example, 
```lean
#check f x
#check f (f x)
#check f (f (f x))
```
 are all applications of terms to terms.

### Abstractions

Finally, we have **abstractions**, which have the form `λ (x : τ) => e` where `τ` is a type and `e` is a term. The `x` in this expression is said to be `bound` to the abstraction. It is a dummy variable and could be renamed without any change in meaning. For example, the following are terms in the λ-calculus:  
```lean
#check λ (y : A) => y
#check λ (g : A → A) => λ (y : A) => g y
```
 In the first example, the abstraction defines a function that simply returns its argument. In the second example, the abstraction defines a function that takes another function `g` and returns yet another abstraction that takes an object `y` and returns `g` applied to `y`.

Note that the parentheses group to the right, so the second example is equivalent to: 
```lean
#check λ (g : A → A) => ( λ (y : A) => g y )
```
 In Lean, we can also abbreviate a chained lamdba abstractions by writing: 
```lean
#check λ (g : A → A) (y : A) => g y
```
 ### Equivalence with `def`

A lambda abstraction is basically an unamed function. You could also give your functions names and use `def`. 
```lean
def inc₁ (x : Nat) : Nat := x + 1
def inc₂ := λ x => x + 1

#eval inc₁ 3
#eval inc₂ 3
#eval (λ x => x + 1) 3
```
 ### Currying

Consider the lambda abstraction 
```lean
variable (X : Type)
variable (a : X)

#check λ (g : X → X) => λ (x: X) => g x
```
 If we apply the abstraction to particular function, then we get another function. 
```lean
#reduce (λ (g : X → X) => λ (x: X) => g x) (λ x => x)
```
 This way this new function is obtained is called _Currying_ after Haskel Curry. The function can then be applied again: 
```lean
#reduce (λ (g : X → X) => λ (x: X) => g x) (λ x => x) a
```
 ## Type Derivation

All **terms have types**. These can be found using type theory's **derivation rules**:

**VAR**: Variables are declared either globally to have a given type (using Lean's variable command) or are bound in a λ-expression.

**ABST**: The type of an abstraction is always of the form A → B where A is the type of the argument and B is the type of the result.

**APPL**: If f : A → B and x : A, then the type of the application of f to x is B.

These derivation rules are applied automatically by Lean in the process of type checking using the #check directive. We can see the types Lean derives as follows. 
```lean
def h₁ := λ (y : A) => y
def h₂ := λ (g : A → A) => λ (y : A) => g y

#check x
#check h₁
#check h₂
#check h₁ x
#check h₂ h₁               --> Example of currying
#check h₂ h₁ x
```
 Note: Currying is named after the Logician Haskel Curry, who studied Electrical Engineering at MIT in the 1920s, although he eventually switched to Physics. 
 ## Type Errors

The typed lambda calculus disallows expressions that do not follow typing rules. For example, the following expression produces a type error 
```lean
#check_failure λ (g : A) => λ (y : A) => g y
```
 because g is not declared to be a function type and therefore cannot be applied to y.

Another example is 
```lean
#check_failure λ (y : A) => q
```
 about which Lean complains because q has not been declared in the present context.

## Judgements and Contexts

When you hover over a #check directive, Lean shows the results of the type derivation as what is called a **judgement**. It is an expression in two parts separated by a **turnstile** ⊢. For example: `#check h₁ x` produces

```
x : A
f : A → A
⊢ A
```

Before the turnstile is the **context**, a list of all the variables introduced so far. After the turnstile is the type of (h₁ x), which in this case is A. In the literature, this written:

```
{ x : A, f : A → A }  ⊢  h₁ x : A
```

which reads: "If A has type A and f has type A → A, then we can derive h₁ x has type A". In an expression such as

```
λ (y : A) => f y
```

the variable f is not bound to an enclosing lambda. In this case it is called **free**. The variable y on the other hand is `bound`. Free variables have to be declared in Lean for expressions to use them. And they have to have types consistent to how they are used. When this is done properly, you will see the free variable declarations in the context part of Lean's results.

## Beta Reduction

An abstraction can be `applied` to another term to produce a new term. This is called β-reduction. It is defined like this:

```
(λ (x:α) => M) N   —β→   M[x:=N]
```

The notation `M[x:=N]` means: take all **free** occurances of `x` in `M` and replace them with the expression N. We have to be careful that `N` does not use the variable `x` freely. Lean does this internally for us The bound version of `x` above is, internally, a completely unique variable that is just displayed as `x` for our convenience.

To apply β-reduction in Lean, you can use the #reduce directive. For example, we can see that
```
(λ (g : α → α) => λ (y : α) => g y) f   —β→   λ (y : α) => f y
```
This is obtained by replacing `g` in `g y` with `f`, as the rule describes. You can have Lean do this for you using the #reduce directive. The `#reduce` directive needs permission to be aggressive, which we can do using the `(types := true)` option. 
```lean
#reduce (types:=true) (λ (y : A) => y) x
#reduce (types:=true) (λ (g : A → A) => λ (y : A) => g y) (λ (y : A) => y)
#reduce (types:=true) (λ (g : A → A) => λ (y : A) => g y) (λ (y : A) => y) x
```
 ## Properties of the Simply Typed λ-calculus

Some interesting observations are in order. We won't prove these here, but they are good to know:

**Uniqueness of Types**: Every term has exacly one type.

**Subject Reduction Lemma**: If `M₁ : α and M₁ —β→ M₂` then `M₂ : α`. That is, beta reduction does't change the type of expressions. It just simplifies them.

**Church-Rosser Theorem**: If `M —β→ N₁` and `M —β→ N₂` then there is some `N₃` such that `N₁ —β→ N₃` and `N₂ —β→ N₃`. That is, it doesn't matter what order you β-reduce an expression's sub-expressions in, you always end up with the same term.

**Strong Normalization**: β-reduction eventually stops at an irreducible term. This is a very strong statement. In most programming languages, you can write infinite loops. But not in the simply typed λ-calculus!



## Extended Example: Church Numerals

Even though the simply typed λ-calculus looks simple, you can encode quite a bit of math with it. The goal of this next section is to show you how do do arithmetic with only what we have so far (simple arrow types and terms depending only on terms). We do this not because it is efficient -- it isn't! Instead, we want to show that the essence of arithmetic is captured by the simply typed λ-calculus.

First, we need a way to represent numbers. Church devised the following scheme, where c₀ is the **Church Numeral** for 0 and so on. 
```lean
def α := Type

def c₀ := λ ( f : α → α ) => λ ( x : α ) => x
def c₁ := λ ( f : α → α ) => λ ( x : α ) => f x
def c₂ := λ ( f : α → α ) => λ ( x : α ) => f (f x)
def c₃ := λ ( f : α → α ) => λ ( x : α ) => f (f (f x))
```
 You can check the type of a Church numeral: 
```lean
#check c₂
```
 For convenience, let's give this type a name: 
```lean
def N := (α → α) → α → α

#check N
```
 ### Arithmetic

We can define functions on numbers. For example, the successor function is defined below. 
```lean
def succ := λ (m : N) => λ (f : α → α) => λ (x: α) => f (m f x)
```
 To see how this works, let's apply succ to c₀. We omit the types to make it easier to read. Note for clarity we use the dummy variables g and y in c₀ instead of f and x.

  succ c₀ = ( λ m => λ f => λ x => f (m f x) )  ( λ g => λ y => y )
          —β—> λ f => λ x => f ( ( λ g => λ y => y ) f x )
                          [note, g is not used, so f x disappears]
          —β—> λ f => λ x => f ( ( λ y => y ) x )
          —β—> λ f => λ x => f x
          = c₁

This is a lot of work, so let's let Lean do this for us: 
```lean
#reduce (types := true ) succ c₀
#reduce (types := true ) succ c₃
```
 ### Other Operations

We can also add two numbers together: 
```lean
def add := λ (m : N) => λ (n : N) => λ (f : α → α) => λ (x: α) => m f (n f x)

#reduce (types := true) add c₃ c₂
#reduce (types := true) add (succ c₃) (add c₁ c₂)
```
 And here is multiplication: 
```lean
def mul :=  λ (m : N) => λ (n : N) => λ (f : α → α) => λ (x: α) => m (n f) x

#reduce (types := true) mul c₃ c₂
```
 We can even do a sort of if-statement: 
```lean
def ifzero := λ (m : N) => λ (n : N) => λ (p : N) =>
              λ (f : α → α) => λ (x: α) =>
              n (λ ( y : _ ) => p f x) (m f x)

#reduce (types := true) ifzero c₂ c₀ c₃
#reduce (types := true) ifzero c₂ c₁ c₃
```
 ### LEAN CAN PROVE 1+1 = 2 
```lean
theorem one_plus_one_is_two : add c₁ c₁ = c₂ :=
  rfl
```
 You can prove this by rfl because, as we will see, two lambda expressions that beta reduce to the same thing are considered `definitionally equal`. Although this is not scalable and in fact Lean has a much more expressive type system that we will harness soon.


/- ## References

Alonzo Church
[An Unsolvable Problem of Elementary Number Theory](https://www.jstor.org/stable/2371045).
American Journal of Mathematics, 1936.

Haskell B Curry
[The Inconsistency of Certain Formal Logics](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/inconsistency-of-certain-formal-logics/FF38B653569E479408EC4DDD26DD7918).
The Journal of Symbolic Logic, 1942.

Alonzo Church
[A formulation of the simple theory of types](http://www.classes.cs.uchicago.edu/archive/2007/spring/32001-1/papers/church-1940.pdf).
Journal of Symbolic Logic, 1940

Uwe Nestmann and Students
[The Lambda Cube Unboxed](https://www.youtube.com/playlist?list=PLNwzBl6BGLwOKBFVbvp-GFjAA_ESZ--q4).
YouTube, 2020




<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
