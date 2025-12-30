import Mathlib

namespace LeanW26.Simple

/-
Simple Types
===

The Simply Typed Lambda Calculus
===

The `simply typed lambda calculus` is an extremely simple programming language
that nevertheless captures the essence of computation. We assume a base type.
In Lean the base type is called `Type`. -/

#check Type

/- Lean tells you `Type` has `Type 1`, so `Type` is a synonym for `Type 0`.
One constructs new types using the arrow → as in the following examples: -/

#check Type → Type
#check Type → (Type → Type)
#check (Type → Type) → Type
#check (Type → Type) → (Type → Type)

/- Arrow `→` associates to the right. So the second expression
above is equivalent to `Type → Type → Type`. -/


/-
Type Variables
===

You define type variables using `def` -/

--hide
section
--unhide

def A := Type
def B := Type → Type
def C := A → B

/- Which looks a bit more like what you would see in a textbook on type theory.
Now you can construct more types. -/

#check A → B → C

--hide
end
--unhide




--hide
section
--unhide

/-
Terms : Variables
===

Next, we define the terms of the lambda calculus.

We start with **variables**, for example `x` and `f`,
which we declare in Lean as follows: -/

variable (x : A)               -- declare a variable x of type a
variable (f : A → A)           -- declare a function f from A into A

#check x
#check f

/-  Here. `x` is a simple object with type `A`, while `f` is an function type from `A` into `A`.


Terms : Applications
===

**Applications** have the form `e₁ e₁` where `e₁` and `e₂` are terms.
For example, -/

#check f x
#check f (f x)
#check f (f (f x))

/- are all applications of terms to terms. -/





/-
Terms: Abstractions
===

**Abstractions** have the form `λ (x : τ) => e` where `τ` is a type and `e` is a term.
The variable `x` in this expression is said to be **bound** to the abstraction.

The following are terms in the λ-calculus:  -/

#check fun (y : A) => y
#check fun (g : A → A) => fun (y : A) => g y

/- In the first example, the abstraction defines a function that simply returns its argument.
In the second example, the abstraction defines a function that takes another
function `g` and returns yet another abstraction that takes an object `y` and
returns `g` applied to `y`.

Parentheses group to the right, so the second example is equivalent to: -/

#check fun (g : A → A) => (fun (y : A) => g y)

/- We abbreviate a chained lamdba abstractions by writing: -/

#check fun (g : A → A) (y : A) => g y




/-
Equivalence with `def`
===

A lambda abstraction is an unamed function.
Give your functions names and use `def`. -/

def inc₁ (x : Nat) : Nat := x + 1
def inc₂ := fun (x : Nat) => x + 1

#eval inc₁ 3
#eval inc₂ 3
#eval (fun (x : Nat) => x + 1) 3






/-
Currying
===

Consider the abstraction -/

variable (a : Type)
def r₁ := fun (g : Type → Type) => fun (x: Type) => g x

/- If we apply the abstraction to particular function, then we get another function. -/

def r₂ := r₁ (fun x => x)

/- Which we can apply again -/

def r₃ := r₂ a

#check r₃ -- Type

/- In this example, `r₂` is a curried expression:
It has "ingested" a function `(fun x => x)` and can then apply this function
to subsequenct arguments.

Currying is named after the Logician Haskel Curry, who
studied Electrical Engineering at MIT in the 1920s (although he eventually
switched to Physics).

 -/

--hide
end
--unhide

/-
Exercises
===

<ex /> Show that `→` is not associative by defining lambda calculus expressions with types
- `Type → (Type → Type)`
- `(Type → Type) → Type`

Use `#check` to make sure your functions have the desired types.
*Challenge:* Define the second expression without using free variables.

<ex /> The functin `String.append` has the type `String → String → String`.
Define a new function `prepend_label` that prepends the string "STRING: "
to its argument by currying `String.append`. Test your function.

-/




/-
Type Derivation
===

All **terms have types**. These can be found using these **derivation rules**:

- **VAR**: Variables are declared either globally to have a given type
(using Lean's variable command) or are bound in a λ-expression.

- **ABST**: The type of an abstraction is always of the form `A → B`
where `A` is the type of the argument and `B` is the type of the result.

- **APPL** If `f : A → B` and `x : A`, then the type of the application of `f`
to `x is B`.

We can see the types Lean derives.. -/

variable (x : A) (f : A → A)
def h₁ := fun (y : A) => y
def h₂ := fun (g : A → A) => fun (y : A) => g y

#check x                   --> A
#check h₁                  --> A → A
#check h₂                  --> (A → A) → A → A
#check h₁ x                --> A
#check h₂ h₁               --> A → A via currying
#check h₂ h₁ (f x)         --> A



/-
Type Errors
===

The typed lambda calculus disallows expressions that do not follow typing rules.
For example, the following expression produces a type error -/

#check_failure fun (g : A) => fun (y : A) => g y

/- because `g` is not declared to be a function type and therefore cannot be applied to `y`.

Another example is -/

#check_failure fun (y : A) => q

/- about which Lean complains because `q` has not been declared in the present context. -/


/-
Judgements and Contexts
===

When you hover over a `#check` directive, Lean shows the results of the type derivation
as what is called a **judgement**. It is an expression in two parts separated by a
**turnstile** `⊢`. For example: `#check h₁ x` produces

```lean
  x : A
  f : A → A
  ⊢ A
```

Before the turnstile is the **context**, a list of all the variables
introduced so far. After the turnstile is the **goal state**,
in this case is `A`, which is the type of `(h₁ x)`.

In the literature, this written:

```text
{ x : A, f : A → A }  ⊢  h₁ x : A
```

which reads: "If A has type A and f has type A → A, then we can derive h₁ x has type A". -/



/-
Exercises
===

<ex /> Create a context and goal state in Lean that matches:
```text
{ a : A, b : B, f : A → B }  ⊢  f a : B
```

Note: If you put

```lean
section
--- code here
end
```

Around all previous examples, then the variables defined remain
local to that section. The source code to this slide deck does this.

-/




/-
Free Variables
===
In an expression such as

```lean
fun (y : A) => f y
```

the variable `f` is not bound to an enclosing lambda. In this case it is called **free**.

The variable `y` on the other hand is **bound**.

Free variables have to be declared in Lean for expressions to use them.
And they have to have types consistent to how they are used.
When this is done properly, you will see the free variable declarations
in the context part of Lean's results. -/




/-
Beta Reduction
===

An abstraction can be **applied** to another term to produce a new term.
This is called β-reduction. It is defined like this:

```
(fun (x:α) => M) N   —β—>   M[x:=N]
```

The notation `M[x:=N]` means: take all `free` occurances of `x` in `M` and
replace them with the expression `N`.

We have to be careful that `N` does not use the variable `x` freely.

Lean does this internally for us The bound version of `x` above is,
internally, a completely unique variable that is just displayed as `x` for our convenience.

Beta Reduction in Lean
===

To apply β-reduction in Lean, you can use the `#reduce` directive. For example,

```
(fun (g : α → α) => λ (y : α) => g y) f   —β—>   λ (y : α) => f y
```

is obtained by replacing `g` in `g y` with `f`, as the rule describes.

You can have Lean do this for you using the `#reduce` directive.

The `#reduce` directive needs permission to be aggressive,
which we can do using the `(types := true)` option. -/

#reduce (types:=true) (fun (y : A) => y) x

#reduce (types:=true) (fun (g : A → A) => fun (y : A) => g y)
                      (fun (y : A) => y)

#reduce (types:=true) (fun (g : A → A) => fun (y : A) => g y)
                       (fun (y : A) => y) x








/-
Properties of the Simply Typed Lambda Calculus
===

Some interesting observations are in order. We won't prove these here, but they are good to know:

- **Uniqueness of Types** Every term has exacly one type.

- **Subject Reduction Lemma** If `M₁ : α` and `M₁ —β—> M₂` then `M₂ : α.`
That is, beta reduction does't change the type of expressions. It just simplifies them.

- **Church-Rosser Theorem** If `M —β—> N₁` and `M —β—> N₂` then there is some `N₃`
such that `N₁ —β—> N₃` and `N₂ —β—> N₃`.
That is, it doesn't matter what order you β-reduce an expression's
sub-expressions in, you always end up with the same term.

- **Strong Normalization** β-reduction eventually stops at an irreducible term.
This is a very strong statement. In most programming languages,
you can write infinite loops. But not in the simply typed lambda calculus!

-/


/-
Exercises
===

<ex /> In the Simply Typed Lamdbda Calculus, the proof that β-reduction is strongly
normalizing shows that every step of β-reduction reduces the following measure:

```text
          1                       if M is a variable
Size(M) = 1 + Size(M₁) + Size(M₂) if M = M₁ M₂
          1 + Size(M')            if M = λ x . M'
```

where `M` is an expression.

Suppose `x : A`. Define a lambda calculus expression `M` such that `Size(M) = 5` and
`M` β-reduces to `x`.

-/



/-
Example: The Church Numerals
===

You can program arithmetic in captured by the λ-calculus.

Church devised the following scheme to represent numbers,
where `c₀` is the Church Numeral for `0` and so on. -/

def α := Type
def c₀ := fun ( f : α → α ) => fun ( x : α ) => x
def c₁ := fun ( f : α → α ) => fun ( x : α ) => f x
def c₂ := fun ( f : α → α ) => fun ( x : α ) => f (f x)
def c₃ := fun ( f : α → α ) => fun ( x : α ) => f (f (f x))

/- You can check the type of a Church numeral: -/

#check c₂      -- (α → α) → α → α

/- For convenience, let's give this type a name: -/

def N := (α → α) → α → α








/-
Arithmetic
===

We can define functions on numbers. For example, the successor function is defined below. -/

def succ := fun (m : N) (f : α → α) (x: α) => f (m f x)

/- To see how this works, let's apply succ to c₀. We omit the types to make it
easier to read. Note for clarity we use the dummy variables g and y in c₀ instead of f and x.

```lean
  succ c₀ = ( λ m => λ f => λ x => f (m f x) ) ( λ g => λ y => y )
          —β—> λ f => λ x => f ( ( λ g => λ y => y ) f x )
                          [note, g is not used, so f x disappears]
          —β—> λ f => λ x => f ( ( λ y => y ) x )
          —β—> λ f => λ x => f x
          = c₁
```

This is a lot of work, so let's let Lean do this for us: -/

#reduce (types := true ) succ c₀
#reduce (types := true ) succ c₃








/-
Addition and Multiplication
===

We can also add two numbers together: -/

def add := fun (m : N) (n : N) (f : α → α) (x: α) => m f (n f x)

#reduce (types := true) add c₃ c₂
#reduce (types := true) add (succ c₃) (add c₁ c₂)

/- And here is multiplication: -/

def mul :=  fun (m : N) (n : N) (f : α → α) (x: α) => m (n f) x

#reduce (types := true) mul c₃ c₂

/-
Booleans and If Statements
===

We can encode an if-statement: -/

def ifzero := fun (m : N)  (n : N) (p : N) =>
              fun (f : α → α) (x: α) =>
              n (fun ( y : _ ) => p f x) (m f x)

#reduce (types := true) ifzero c₂ c₀ c₃
#reduce (types := true) ifzero c₂ c₁ c₃







/-
1+1 = 2
===
-/

theorem one_plus_one_is_two : add c₁ c₁ = c₂ :=
  rfl

/- You can prove this by the reflexive property of equality (`rfl`)
because two λ-expressions that beta reduce to the same thing are
considered **definitionally equal**.

Of course, Church Numerals are a very clunky way to define numbers and operators.

To represent more mathematics more elegantly, we need more types! -/





/-
Exercises
===

<ex /> Define a lambda abstraction, called double, that takes a Church numeral
and doubles it. Evaluate it on a few examples.

 -/



/-
Type Inference
===

Lean is good at type inference. We can go a step further with Lean and leave out
types in expressions. -/

#check fun _ y => y
#check fun ( g : α → α ) y => g y
#check fun ( g : α → α ) y => g (g y)

/- We can also write the other operations, like multiplication, more concisely: -/

#check λ (m n : N) f x => m (n f) x

/- We can't leave out all of the type information though. Consider: -/

#check_failure λ g y => g y

/- In the above, there are any number of ways types could be assigned to g and y, so Lean
complains that it can't assign types to them.




Self Application is Untypeable
===

Dropping types for the moment, define the term
```
Ω := λ x => x x
```
and consider `Ω` applied to itself:
```
(λ x => x x) (λ x => x x)       —β—>       (λ x => x x) (λ x => x x)
```
producing an infinite loop. Suppose you could give `M M` a type, say `α`.
Then `M` has to be a function `M : τ → σ`

But since `M` is operating on itself, `M` has to be of type τ:
```
M : τ
```
So `M `has two different types, which is not possible. Lean is not able to find
a type for `x`. The placeholder symbol `_` is used by Lean as a way to ask the type
checker to infer a type. -/

#check_failure (λ (M:_) => M M)






/-
Proposition
===

Lean has a special type called Prop which stands for **Proposition**.
It treats this type somewhat differently than all other types, but in
most ways it ist just another type. -/

variable (p : Prop)
#check Prop
#check p

/- If p is of type Prop, then an element `hp : p` is evidence that the
type `p` is not empty. Alternatively, you can think of hp as a `proof` of `p`.



Arrow Types on Props are Implications
===

Arrow types which above denoted functions, can be
thought of as denoting **implication** if Prop is involved.  -/

#check p → p

/- Armed with the lambda calculus and we can now prove theorems involving implication: -/

example (p : Prop) : p → p :=
  fun hp => hp

example (p q : Prop) : p → (p → q) → q :=
  fun hp => fun hpq => hpq hp



--hide

/-
Looking Ahead: The Curry Howard Isomorphims
===

The most important problem in using type theory for proofs is INHABITATION,
followed by TYPE CHECKING. We will see later the following
remarkable fact, called the Curry-Howard corresponence, which says that in
the judgement `Γ ⊢ M : σ`,

  `Γ` can be considered a set of givens or assumptions
  `σ` can be considered a mathematical statement like a theorem or lemma
  `M` can be considered a proof of the theorem assuming the statements in `Γ`.

Thus, type checking amounts to checking that `M` is a proof of `σ`,
which is a relatively straightfoward problem.

This is why tools like Lean are called `proof assistants`. They check to make sure
your proofs are correct.

On the other hand, type inhabitation amounts to finding a proof of σ.


Functions and Implication Again
===

Going a step further, we'll see that an abstraction
```lean
fun p : σ => q
```
which may have type
```lean
σ → τ
```
is the general form of a proof of the statement `σ → τ` where `→` means "implies".
It can be thought of as a transformation taking a proof of `σ`, which one assumes
is available, and returning a proof of `τ`, which is thought of as a goal to be
proved. Writing the details of what `q` is amounts to programming.

By building on it, as Lean and similar tools do, one can enocde an astonishingly
large set of all of mathematics, and presumably knowledge in general.
We'll learn how to take advantage of the Curry-Howard corresponence soon.

 -/


--unhide


/-
Exercises
===

<ex /> The following lamdba calculus expressions do not type check in Lean.

```lean
  fun x y => x y
  fun x y z => x y z
  fun x y => y (y (y x))
  fun x y z => (y x) z
```

Rewrite them by giving the variables types. Use #check to make sure they work.

<ex /> The [Wikipedia Page](https://en.wikipedia.org/wiki/Church_encoding) on
Church Encodings shows how to define various other types and operations using
only the Simply Typed Lambda Calculus. Choose an interesting example,
show how to define it in Lean, and test it on a few examples. In your solution,
make sure to write a few sentences on what you are doing.

-/


--hide
end LeanW26.Simple
--unhide
