
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Types.lean'>Code</a> for this chapter</span>
 # Basic Type Theory

In the previous chapter we defined the integers in terms of the λ-calculus. You can define other opertations on the natural numbers in a similar fashion. It is also fairly straightforward to define Booleans and Boolean Logic, as well as a number of other basic mathematical structures.

Building up from these basic ideas to more complex mathematics is the point of Lean. Eventually, we will arrive at cutting edge mathematics in Lean. Because it is defined in terms of thee basic building blocks, we always have a proof that goes from the high level mathematica statements to the low level meaning in terms of the typed λ-calculus: That is, a proof from first princples.

That said, it will ultimately be better to define a richer set of types, which is what this chapter covers. Eventually, we'll define the natural numbers and almost every other mathematical object in Lean using what are called [Inductive Types](InductiveTypes.md).

## Type Theory Questions

Now that we have a simple programming language and a way to assign types to terms in that language, we can explore a number of problems in type theory, each with its own purpose and challenges.

**TYPE CHECKING**: In a given context, does a term M have a given type σ?
```
Γ ⊢ M : σ
```

**WELL TYPEDNESS**: Does there exist a context in which a type be assigned to a term M? Another way of saying this is "is M a legal term?"

```
? ⊢ M : ?
```

**TYPE INFERENCE**: Can M be assigned a type consistent with a given context?
```
Γ ⊢ M : ?
```

**INHABITATION**: Does there exist a term of a given type? If σ is a logical statement, then this is the question of whether σ has a proof.
```
Γ ⊢ ? : σ
```

# Type Inference

Lean is good at type inference. We can go a step further with Lean and leave out types in expressions, letting Lean infer what they must be. For example, the Church numerals can be written more consicely, skipping some of the type declarations and using multi-argument lambdas, as follows: 
```lean
#check λ _ y => y
#check λ ( g : α → α ) y => g y
#check λ ( g : α → α ) y => g (g y)
```
 We haven't said what the type of y is in these expressions. And we haven't even given the first bound variable in c₀ a name, since it isn't used in the the body of the abstraction. Lean infers that y must have type α because it is being acted upon by a function from α to α. We can also write the other operations, like multiplication, more concisely: 
```lean
#check λ (m n : N) f x => m (n f) x
```
 We can't leave out all of the type information though. Consider: 
```lean
#check_failure λ g y => g y
```
 In the above, there are any number of ways types could be assigned to g and y, so Lean complains that it can't assign types to them. So while the expression is typeable, Lean can't infer a type for it and you have to give it more information.

### Self-application is Untypeable

Dropping types for the moment, define the term
```
Ω := λ x => x x
```
and consider `Ω` applied to itself `Ω`:
```
(λ x => x x) (λ x => x x)       —β—>       (λ x => x x) (λ x => x x)
```
producing an infinite loop. Suppose you could give `M M` a type:
```
M M : σ
```
For this to work, `M` has to be a function:
```
M : τ → σ
```
But since `M` is operating on itself, `M` has to be of type `τ`:
```
M : τ
```
So `M` has two different types, which is not possible. Lean is not able to find a type for `x`. The placeholder symbol `_` is used by Lean as a way to ask the type checker to infer a type. 
```lean
#check_failure (λ (M:_) => M M)
```
 ## Propositions

Lean has a special type called `Prop` which stands for `Proposition`. It treats this type somewhat differently than all other types, but in most ways it ist just another type. 
```lean
variable (p : Prop)
#check Prop
#check p
```
 If p is of type `Prop`, then an element `hp : p` is evidence that the type p is not empty. Alternatively, you can think of hp as a `proof` of p.

Furthermore, arrow types which above denoted functions, can be thought of as denoting **implication** if `Prop` is involved.  
```lean
#check p → p
```
 Armed with the lambda calculus and we can now prove theorems involving implication: 
```lean
example (p : Prop) : p → p :=
  λ hp => hp

example (p q : Prop) : p → (p → q) → q :=
  λ hp => λ hpq => hpq hp
```
 ## Why is it Called "Simply Typed"?

You might be asking yourself, is there a non-simply typed λ-calculus? The answer is yes! We will get there eventually. Here's a preview:

**Simple types:** Terms depend on other tems. This is what we've covered so far. For example, the body of a lambda abstraction (a term) depends on the bound variable (also a term). 
```lean
#check (λ x : Nat => x+1) --- the term x+1 depends on the term x.
```
 **Polymorphism:** Terms can depend on types. Polymorphism allows us to write functions that operate on a variety of types, instead of just a single type, by taking the type to be operated on as an argument. For example, the identity function `λ x : A => x` only operates on elements of type x. What if we wanted to define an arbitrary identity function for any type. Here is one way: 
```lean
#check (λ α : Type => λ x : α => x) -- a polymorphic identity function.
```
 A better way would be: 
```lean
universe u
def my_id {α : Type u} (x : α) := x

#check my_id 1
#check my_id "one"
#check my_id my_id
```
 Note the curly braces around `α : Type u` specify that the argument `α` is _implicit_. That is, that Lean should try to infer what it is. In the the examples `#check` statements above, Lean figures out which type the argument is, and therefor which type the overall expression is, by inspection.

**Parameterized Types:** Types can depend on types. The idea here is to build a type from other types. For example, a List type is fine, but it would nice to avoid having two make a separate data type for lists of different types of objects. In fact, Lean's standard library defines `List` as a parameterized type. You can see in the first `#check` below that making a list requires a type as an argument 
```lean
#check List            -- Requires a type as an argument
#check List Nat        -- The type of a list of natural numbers
#check List (List Nat) -- The type of a a list of list of natural numbers
```
 Lean is also good at figuring out what kind of list you are talking about in most contexts, as the following examples show. 
```lean
#check [1,2,3]
#check ["one","two","three"]
```
 **Dependent types:** Types can depend on terms. Finally, we can have types that depend on terms. For example, the type of vectors (from Lean's standard library) of natural numbers of length 10 depends on the term 10. 
```lean
#check Vector Nat 10 -- Vectors of 10 Nats
```
 **Calculus of Constructions:** If we allow all of the above in type theory, we get what is called the Calculus of Constructions, or CoC. This theory was first described by Thierry Coqrand and emboded in the Coq proof assistant, now called Rocq. Lean and other proof assistants are also based on CoC.

**Inductive Types**: Types can be defined inductively. For example, the natural numbers are defined by a base case (zero) and a successor function (succ), from which all other natural numbers can be constructed. This is discussed in more detail in the chapter on [Inductive Types](./InductiveTypes.md).

**Quotients**: Quotients of types via equivalence relations. For example, a real number is defined to be the set of all Cauchy sequences of rational numbers that converge to it. That is, the reals are the quotient of the set of Cauchy Sequences by Cauchy equivalence. A great example of quotients is covered in the chapter on the  [Integers](./Integers/Intro.md).

## Looking ahead: the Curry-Howard Correspondence

The most important problem in using type theory for proofs is INHABITATION, followed by TYPE CHECKING. To motivate why, we will see later the following remarkable fact, called the Curry-Howard corresponence, which says that in the judgement Γ ⊢ M : σ,

- Γ can be considered a set of givens or assumptions
- σ can be considered a mathematical statement like a theorem or lemma
- M can be considered a proof of the theorem assuming the statements in Γ.

Thus, type checking amounts to checking that M is a proof of σ, which is a relatively straightfoward problem and we have seen that Lean is quite good at it. This is why tools like Lean are called `proof assistants`. They check to make sure your proofs are correct.

On the other hand, type inhabitation amounts to finding a proof of σ. This is a very difficult problem, essentially the job of the working mathematician. From a computational point of view, finding a proof means searching over terms M until one finds one that has type σ. Depending on how expressive the programming language for terms is, this can either be a computationally intractable problem (meaning search is the best you can do) or it can be a computationally unsolvable problem (meaning there may not be an algorithm that is guaranteed to find an M of type σ). Both of these observations are job security for mathematicians!

Going a step further, we'll see that an abstraction
```
λ p : σ => q
```
which may have type
```
σ → τ
```
is the general form of a proof of the statement σ → τ where → means "implies". It can be thought of as a transformation taking a proof of σ, which one assumes is available, and returning a proof of τ, which is thought of as a goal to be proved. Writing the details of what q is amounts to programming.

As a computer scientist myself it is very satisfying to know that programming functions with given type specifications is _the same thing as_ proving theorems!

This idea is not merely cute. By building on it, as Lean and similar tools do, one can enocde an astonishingly large set of all of mathematics, and presumably knowledge in general. We'll learn how to take advantage of the Curry-Howard corresponence soon.

## Exercises


<span></span> 1) Define a lambda abstraction, called double, that takes a Church numeral and doubles it. Evaluate it on a few examples.


<span></span> 2) The following lamdba calculus expressions do not type check in Lean. 
```lean
#check_failure λ x y => x y
#check_failure λ x y z => x y z
#check_failure λ x y => y (y (y x))
#check_failure λ x y z => (y x) z
```
 Rewrite them by giving them variables types. Use #check to make sure they work.


<span></span> 3) Prove the following example using only lambda calculus expressions 
```lean
example (p q : Prop) : p → q → p → q → p := sorry
```


<span></span> 4) Show two different lambda calculus proofs of the following example. Hint, compare the form of the proposition to the Church numerals.
```lean
example (p : Prop) : (p → p) → p → p := sorry
```

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
