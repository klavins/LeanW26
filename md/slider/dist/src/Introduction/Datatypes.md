
Datatypes
===


Inductively Defined Types
===


All the types we've been looking at
```lean
ℕ, ℚ, ℝ, List,  ...
```
are *inductively defined*. That means, they are defined by

   - Some number of base cases
   - Some number of recursive constructors

We'll have more to say about the theory of inductive types later.
For now we'll describe them via examples.


Natural Numbers
===
We can redefine the natural numbers with the definition:



<div class="lean-code" data-start-line="40" data-end-line="42"><pre><code>inductive MyNat where
  | zero : MyNat               -- base case
  | succ : MyNat → MyNat         -- recursive constructor</code></pre></div>


opening the namespace MyNat allows us to type `zero` instead of `MyNat.zero`.


<div class="lean-code" data-start-line="48" data-end-line="54"><pre><code>open MyNat

#check zero                  -- 0
#check succ zero             -- 1
#check succ (succ zero)      -- 2
#check zero.succ             -- alternative syntax for 1
#check zero.succ.succ        -- alternative syntax for 2</code></pre></div>


This is how you build the natural numbers in Lean. The numerals 0, 1, 2, etc.
are just "syntactic sugar".
 

<div class="lean-code" data-start-line="61" data-end-line="62"><pre><code>#eval Nat.zero == 0                      -- True
#eval Nat.zero.succ.succ.succ == 3       -- True</code></pre></div>


Complex Numbers
===

Many types are inductive. For example, here is a complex number:


<div class="lean-code" data-start-line="71" data-end-line="74"><pre><code>inductive MyComplex where
  | mk : Real → Real → MyComplex

#check MyComplex.mk 1 2       -- 1 + 2i</code></pre></div>

 Recall that you can match the way an inductive type was constructed. 

<div class="lean-code" data-start-line="78" data-end-line="87"><pre><code>def MyComplex.re (x : MyComplex) : Real :=
  match x with
  | mk a _ =&gt; a

def MyComplex.im (x : MyComplex) : Real :=
  match x with
  | mk _ b =&gt; b

noncomputable      -- Real.sqrt is non-computable
def MyComplex.abs (x : MyComplex) : Real := Real.sqrt (x.re^2 + x.im^2)</code></pre></div>


Three Valued Logic
===

Not all inductive types have _recursive_ constructors. `Bool` has only base cases.
Here's a similar example:


<div class="lean-code" data-start-line="97" data-end-line="111"><pre><code>inductive TriBool where
  | T : TriBool
  | F : TriBool
  | U : TriBool

open TriBool

def and (A B : TriBool) :=
  match A, B with
  | T, x   =&gt; x
  | F, _   =&gt; F
  | U, F   =&gt; F
  | U, _   =&gt; U

#eval and T (and U F)   -- F</code></pre></div>


Option
===

The `Option` type is useful in situations where a value might not be available.
This is an example of an inductive type that depends on another type.



<div class="lean-code" data-start-line="123" data-end-line="125"><pre><code>inductive MyOption (A : Type)
  | none : MyOption A
  | some : A → MyOption A</code></pre></div>

 In the definition below, Lean knows the return type is `Option`. Thus,
we can use the `.` notation to call methods in the `Option` namespace
when in the expression. 

<div class="lean-code" data-start-line="131" data-end-line="134"><pre><code>def first {A : Type} (L : List A) : Option A :=
  match L with
  | [] =&gt; .none
  | x :: _ =&gt; .some x</code></pre></div>

 Some examples: 

<div class="lean-code" data-start-line="138" data-end-line="139"><pre><code>#eval first [1,2,3]             -- some 1
#eval first ([]:List Int)       -- none</code></pre></div>


Matching Option
===

You can use match to get the value of an `Option`, if it exists. 

<div class="lean-code" data-start-line="147" data-end-line="151"><pre><code>def my_func (L : List ℕ) : List ℕ :=
  let x := first L
  match x with
  | .some x =&gt; [x,x+1]
  | .none =&gt; [0,1]</code></pre></div>


`Option` is an example of a `Monad`. A similar Monad is `Except`, which
also takes a string argument. We'll get to these later.


<div class="lean-code" data-start-line="158" data-end-line="158"><pre><code>#check Except</code></pre></div>


Exercises
===

<ex/> Define an alternative complex number in terms of its magnitude and argument.
Note that the type of non-negative reals is defined as `NNReal` in Mathlib.

<ex/> Define `or` for `TriBool`.

<ex /> Lean's rational number type `ℚ` defines `1/0` to be `0`. Define a function
`reciprocal (x : ℚ) : Option ℚ` that returns `none` when `x` is zero.



Binary Trees
===

Here is a an extended example where we define a polymorphic Binary Tree type and
show how to start a library of functions for it. 

<div class="lean-code" data-start-line="184" data-end-line="186"><pre><code>inductive BTree (A : Type) where
  | leaf : A → BTree A
  | node : A → BTree A → BTree A → BTree A</code></pre></div>

 Once a new type is defined, we usually put all of its functions in a *namespace*.
The following line opens that namespace. 

<div class="lean-code" data-start-line="191" data-end-line="194"><pre><code>namespace BTree

#check leaf            -- A → BTree A
#check node            -- A → BTree A → BTree A → BTree A</code></pre></div>


Defining a Binary Tree
===

Here's an example tree.


<div class="lean-code" data-start-line="203" data-end-line="203"><pre><code>def my_tree := node 1 (leaf 2) (node 3 (leaf 4) (leaf 5))</code></pre></div>


<img src="https://docs.google.com/drawings/d/e/2PACX-1vQeSlUTnaC2yPFo8vJgGKOCTcHxq63r2fP37AMPvyMGzSi53ZkclclgY51zSN4D3sCczjretVs3HIQW/pub?w=960&amp;h=720" width=30%>



Defining Functions on Inductive Types
===

Here's an example function to convert tree to a list. 

<div class="lean-code" data-start-line="217" data-end-line="222"><pre><code>def to_list {A : Type} (T : BTree A) : List A :=
  match T with
  | leaf a =&gt; [a]
  | node a left right =&gt; [a] ++ (to_list left) ++ (to_list right)

#eval to_list my_tree   -- [1,2,3,4,5]</code></pre></div>


Representing Values
===

When we define a tree and evaluate it, we get a cumbersome representation:  

<div class="lean-code" data-start-line="230" data-end-line="231"><pre><code>#eval my_tree -- BTree.node 1 (BTree.leaf 2)
              -- (BTree.node 3 (BTree.leaf 4) (BTree.leaf 5))</code></pre></div>

 We can tell Lean to make a more compact representation. First we define a `to_str`
function. It requires that `A` has a `toString` instance we can use (more on this later). 

<div class="lean-code" data-start-line="236" data-end-line="239"><pre><code>def to_str {A : Type} [ToString A] (T : BTree A) : String :=
  match T with
  | leaf a =&gt; toString a
  | node a L R =&gt;  &quot;(&quot; ++ (toString a) ++ &quot; &quot; ++ (to_str L) ++ &quot; &quot; ++ (to_str R) ++ &quot;)&quot;</code></pre></div>

 The we define a _representation_ of a tree (using the representation of `A`).

<div class="lean-code" data-start-line="243" data-end-line="245"><pre><code>instance {A : Type} [Repr A] [ToString A] : Repr (BTree A) := {
  reprPrec := fun T _ =&gt; to_str T
}</code></pre></div>


Now when we evaluate we get: 

<div class="lean-code" data-start-line="250" data-end-line="250"><pre><code>#eval my_tree             -- (1 2 (3 4 5))</code></pre></div>


Mapping to Trees
===

Here is an example function. Note the use of curly braces since `A` and
`B` are inferable from the argument `f`.



<div class="lean-code" data-start-line="262" data-end-line="267"><pre><code>def map {A B : Type} (f : A → B) (T : BTree A) : BTree B :=
  match T with
  | leaf a =&gt; leaf (f a)
  | node a left right =&gt; node (f a) (map f left) (map f right)

#eval map (fun x =&gt; x*x) (node 0 my_tree my_tree)</code></pre></div>

 By the way, since we opened the namespace `BTree`, the functions we defined
are in the `BTree` namespace, accessible after we close it using `.` 

<div class="lean-code" data-start-line="272" data-end-line="275"><pre><code>end BTree

#check BTree.to_list
#check BTree.map</code></pre></div>

 Even better, values of type BTree can use the methods via the `.`. 

<div class="lean-code" data-start-line="279" data-end-line="281"><pre><code>def T : BTree ℕ := BTree.leaf 0

#eval T.map Nat.succ</code></pre></div>


Exercises
===

<ex/> Define a function `swap` that takes a `BTree` and swaps the order of the
children in all nodes. You should get, for example:

```lean
#eval swap my_tree             -- (1 (3 5 4) 2)
```


Mutually Inductive Types
===

Sometimes you want to define two types inductively where the definition of
one depends on the definition of the other. For example:


<div class="lean-code" data-start-line="305" data-end-line="314"><pre><code>mutual
  inductive Ev
  | zero : Ev
  | succ : Od → Ev

  inductive Od
  | succ : Ev → Od
end

#check Ev.succ (Od.succ Ev.zero)</code></pre></div>


Expression Trees
===
A common use case for mutual induction is to define terms and expressions.


<div class="lean-code" data-start-line="322" data-end-line="332"><pre><code>mutual
  inductive Term
  | var : String → Term
  | num : ℕ → Term
  | paren : Expr → Term

  inductive Expr
  | neg : Term → Expr
  | add : Term → Term → Expr
  | mul : Term → Term → Expr
end</code></pre></div>


Here's how you would encode 2*(x+1)


<div class="lean-code" data-start-line="338" data-end-line="339"><pre><code>open Expr Term in
def expr : Expr := mul (num 2) (paren (add (var &quot;x&quot;) (num 1)))</code></pre></div>


Exercises
===

<ex /> Write a function `Expr.CountAdds` that takes an `Expr` and returns the number of
additions in it. You will need an auxiliary function and you will have to put both
definitions in a mutual block, since they call each other.



<div class="lean-code" data-start-line="351" data-end-line="354"><pre><code>mutual
  def Term.CountAdds (t : Term) : ℕ := sorry
  def Expr.CountAdds (e : Expr) : ℕ := sorry
end</code></pre></div>


Structures
===

Recall the pattern for `MyComplex` in which we

- defined an inductive type with a constructor of the form `A → A → A`
- defined accessors with `match x with | mk x y = x`.

That is so common that Lean has a convenience notation:
If you have an inductive type with *one* constructor, then you can use a *structure*.



<div class="lean-code" data-start-line="371" data-end-line="380"><pre><code>structure Komplex where
  re : Real
  im : Real

open Komplex

def conj (x : Komplex) : Komplex:= {
  re := x.re,
  im := -x.im
}</code></pre></div>


Type Hints are Often Required
===

Q: Why do you think this doesn't work

```lean
def conj (x : Komplex) := {
  re := x.re,
  im := -x.im
}
```


Bracket Notation
===

You can use the `⟨ a, b ⟩` if the type is known. For example



<div class="lean-code" data-start-line="404" data-end-line="407"><pre><code>def add (x y : Komplex) : Komplex :=
  ⟨ x.re + y.re, x.im + y.im ⟩

def negate (x : Komplex) : Komplex := ⟨ -x.re, -x.im ⟩</code></pre></div>


Match with Structures
===

You can use structures as though they were inductive types (since they are). 

<div class="lean-code" data-start-line="415" data-end-line="425"><pre><code>def negate1 (x : Komplex) : Komplex :=
  match x with | mk a b =&gt; ⟨ -a, -b ⟩

def negate2 (x : Komplex) : Komplex :=
  match x with | ⟨ a, b ⟩ =&gt; ⟨ -a, -b ⟩

def negate3 (x : Komplex) : Komplex :=
  let ⟨ a, b ⟩ := x
  ⟨ -a, -b ⟩

def negate4 (x : Komplex) : Komplex := ⟨ -x.1, -x.2 ⟩</code></pre></div>


Fields Can Depend on Other Fields
===

For example, here is a type that stores a type and a value of that type.


<div class="lean-code" data-start-line="436" data-end-line="438"><pre><code>structure Dyn where
  α : Type
  val : α</code></pre></div>

 This particular type is useful for making heterogeneous lists. 

<div class="lean-code" data-start-line="442" data-end-line="442"><pre><code>def L : List Dyn := [ ⟨ ℕ, 3 ⟩, ⟨ String, &quot;three&quot;⟩ ]</code></pre></div>


<div class='fn'>Note that <tt>Dyn</tt> is isomorphic to <tt>Σ α, α</tt>,
which is a <tt>Sigma</tt> type, which also has this property.
So we could have written <tt>List (Σ α, α)</tt>.</div>


Structures Can Be Self-Referential
===
Here is an example of a structure that references itself.


<div class="lean-code" data-start-line="457" data-end-line="459"><pre><code>structure Node where
  label : String
  next  : Option Node</code></pre></div>

 An example value is : 

<div class="lean-code" data-start-line="463" data-end-line="467"><pre><code>def chain : Node :=
  {
    label := &quot;a&quot;,
    next  := some { label := &quot;b&quot;, next := none }
  }</code></pre></div>


Note that not using `Option` type checks, but without additional assumptions
has no inhabitants.


<div class="lean-code" data-start-line="474" data-end-line="476"><pre><code>structure Node&#x27; where
  label : String
  next  : Node&#x27;</code></pre></div>


Extending Structures
===

You may also see examples where a structure extends other structures.


<div class="lean-code" data-start-line="489" data-end-line="496"><pre><code>structure A where
  x : ℕ

structure B where
  y : ℕ

structure C extends A, B where
  z : ℕ</code></pre></div>

 A value of type `C` has three fields: 

<div class="lean-code" data-start-line="500" data-end-line="500"><pre><code>def c : C := { x := 1, y := 2, z := 3 }</code></pre></div>


Exercises
===

<ex/> Define a structure `Vector3D`.

<ex/> Define a cross product function of two `Vector3D` terms and test it on examples.



Products
===

Products represent a pair of objects.



<div class="lean-code" data-start-line="522" data-end-line="529"><pre><code>structure MyProd (A B : Type) where
  fst : A
  snd : B

def p : MyProd Rat String := ⟨ 0, &quot;zero&quot; ⟩

#eval p.fst
#eval p.snd</code></pre></div>

 Lean's Prod uses `×`: 

<div class="lean-code" data-start-line="533" data-end-line="533"><pre><code>def q : Rat × String := ⟨ 1, &quot;one&quot; ⟩</code></pre></div>


Using Products
===
We could have defined


<div class="lean-code" data-start-line="541" data-end-line="542"><pre><code>def Komplex&#x27; := ℝ × ℝ
def Komplex&#x27;.re (x : Komplex&#x27;) := x.fst</code></pre></div>


and so on. Or



<div class="lean-code" data-start-line="549" data-end-line="550"><pre><code>def Point {α : Type} := α × α
def Vector3D&#x27; := ℚ × ℚ × ℚ</code></pre></div>

 The benefit is that you get a bunch of defined functions for products.
The downsides are
- the defined type may not really be a cross product space (e.g. complex numbers
have inverses, but pairs don't).
- you have to define a lot of synonyms (e.g. `x.re = x.fst`) anyway.



Π-Types
===

A Π-Type is a generalization of a product. In type theory it is a core object not defined
in terms of some other notion.

An example of a _non-dependent_ `Pi-Type` is the set of infinite sequences of rationals.


<div class="lean-code" data-start-line="570" data-end-line="570"><pre><code>def Qn := Π _n : ℕ, ℚ</code></pre></div>


This is definitionally equal to 

<div class="lean-code" data-start-line="575" data-end-line="575"><pre><code>def Qn&#x27; := (ℕ → ℚ)</code></pre></div>

 An example is 

<div class="lean-code" data-start-line="579" data-end-line="579"><pre><code>def harmonic_sequence : Qn := fun n =&gt; 1/(n+1)</code></pre></div>


Dependent Π-Types
===

To build an example of a _dependent_ Π-type, we first need a _dependent type_,
which is a type that depends on a parameter. For example, `Fin n` is the set of
natural numbers less than `n` (defined in the `Prelude` as a structure).

From `Fin n` we can construct


<div class="lean-code" data-start-line="592" data-end-line="592"><pre><code>def DPT := Π n : ℕ, Fin (n+1)</code></pre></div>

 or equivalently 

<div class="lean-code" data-start-line="596" data-end-line="596"><pre><code>def DPT&#x27; := (n : ℕ) → Fin (n+1)</code></pre></div>


which is the set of sequences `σ` of natural numbers where `σ(n) < n`. For example,


<div class="lean-code" data-start-line="602" data-end-line="603"><pre><code>def σ1 : DPT := fun n =&gt; ⟨ n, by lia ⟩
def σ2 : DPT&#x27; := fun n =&gt; ⟨ n/2, by lia ⟩</code></pre></div>

 Since we haven't covered proofs yet, we'll dig in to these ideas later. 

Sums
===

A sum type represents the _choice_ of value from one of two sets.
So a value is constructed as either "in left" or "in right".



<div class="lean-code" data-start-line="616" data-end-line="626"><pre><code>inductive MySum (A B : Type) where
  | inl : A → MySum A B
  | inr : B → MySum A B

def s1 : MySum Rat String := .inl 0
def s2 : MySum Rat String := .inr &quot;zero&quot;

def swap (s : MySum Rat String) : MySum String Rat :=
  match s with
  | .inl x =&gt; .inr x
  | .inr x =&gt; .inl x</code></pre></div>

 Lean's Sum uses `⊕`: 

<div class="lean-code" data-start-line="630" data-end-line="630"><pre><code>def s : Rat ⊕ String := .inl 1</code></pre></div>


An Alternative ℕ
===

An illustrative use of sums is to build on our definition of Even and Odd numbers with:



<div class="lean-code" data-start-line="640" data-end-line="640"><pre><code>def Naturals := Ev ⊕ Od</code></pre></div>

 Zero and successor can be defined with: 

<div class="lean-code" data-start-line="644" data-end-line="648"><pre><code>def Naturals.zero : Naturals := .inl Ev.zero

def Naturals.succ (x : Naturals) : Naturals := match x with
  | .inl a =&gt; .inr (Od.succ a)
  | .inr a =&gt; .inl (Ev.succ a)</code></pre></div>


Sums as Co-products
===

<img src='img/coprod.jpg' class='img-up-right' width=20%></img>

Suppose we have two disjoint copies of a space `X`. Then `X ⊕ X` <br>
is the type of points in that space. They are either a point <br>
from the "left" side or a point in the "right" side.

For example, to start building an identification topology we might:


<div class="lean-code" data-start-line="663" data-end-line="669"><pre><code>def TwoR := ℝ ⊕ ℝ

def equiv (x y : TwoR) : Prop := match x,y with
  | .inl a, .inl b =&gt; a = b
  | .inr a, .inr b =&gt; a = b
  | .inl a, .inr b =&gt; a = 0 ∧ b = 0
  | .inr a, .inl b =&gt; a = 0 ∧ b = 0</code></pre></div>

 Then show `equiv` is an equivalence relation and take the quotient

```lean
TwoR / equiv
```
We'll get to what this means and how to do it later. 

Σ-Types
===

A Σ-Type represents a choice of an object from a single set. These are defined inductively.

```lean
structure Sigma {α : Type} (β : α → Type) where
  fst : α
  snd : α → β fst
```

Lean provides several equivalent notations:


<div class="lean-code" data-start-line="695" data-end-line="697"><pre><code>def SigT   := Sigma (fun n : ℕ =&gt; Fin n)
def SigT&#x27;  := Σ n : ℕ, (Fin n)
def SigT&#x27;&#x27; := (n:ℕ) × (Fin n)</code></pre></div>

 As an example of a value: 

<div class="lean-code" data-start-line="701" data-end-line="701"><pre><code>def x : SigT := ⟨ 3, 2 ⟩     -- 2 has type Fin 3</code></pre></div>


Exercises
===

<ex /> Rewrite your cross product function in terms of `ℚ × ℚ × ℚ`.

<ex /> You can specify a circle with a single point `r : ℚ` and a rectangle
with a pair of points `x y : ℚ`. Thus a shape might be defined as


<div class="lean-code" data-start-line="713" data-end-line="713"><pre><code>def Shape := ℚ ⊕ (ℚ × ℚ)</code></pre></div>

 define functions `area (s : Shape) : ℚ` and `perimeter (s : Shape) : ℚ`.
Approximate π with `22/7` (or whatever your favorite approximate is).

<div class="lean-code" data-start-line="718" data-end-line="718"><pre><code>#check Real.pi</code></pre></div>


Notation
===

Lean uses user-defined syntax extensively to make code look more like math.

This can make it challenging to figure out what an expression means.

For example, suppose we defined addition as


<div class="lean-code" data-start-line="731" data-end-line="734"><pre><code>def MyNat.add (x y : MyNat) :=
  match x with
  | .zero =&gt; y
  | .succ k =&gt; .succ (MyNat.add k y)</code></pre></div>

 The we can register a syntax directive like: 

<div class="lean-code" data-start-line="738" data-end-line="738"><pre><code>infix:65 &quot; + &quot; =&gt; MyNat.add</code></pre></div>

 so we can write: 

<div class="lean-code" data-start-line="742" data-end-line="742"><pre><code>#eval MyNat.zero.succ + MyNat.zero.succ.succ</code></pre></div>


Notation for Term and Expr
===

Recall our `Expr` class in which `2*x+1` was represented as
```lean
mul (num 2) (paren (add (var "x") (num 1)))
```

At the risk of completely befuddling our user, we can overload some notation.
Here we use _notation classes_ instead of _syntax_ directives.


<div class="lean-code" data-start-line="758" data-end-line="765"><pre><code>open Term Expr

instance : Coe String Term where coe s := Term.var s
instance : HMul Term Term Expr := ⟨ mul ⟩
instance : HMul ℕ Expr Expr := ⟨ fun x y =&gt; mul (num x) (paren y) ⟩
instance : HAdd Term Term Expr := ⟨ add ⟩
instance : HAdd Term ℕ Expr := ⟨ fun x y =&gt; add x (num y) ⟩
instance : Coe Expr Term := ⟨ paren ⟩</code></pre></div>


Now we can write, for example:


<div class="lean-code" data-start-line="771" data-end-line="771"><pre><code>def t1 : Expr := 2 * (var &quot;x&quot; + 1)</code></pre></div>


Notation in Lean is Endless
===

 The ways in which you can define your own syntax in Lean are many and varied.

Pros:
  - You can make expressions easier to read
  - You can make code look more like math

Cons:
  - You can confuse users
  - You have to refactor all your notation when you change your library

In any case, we will introduce these mechanisms as we need them.

See the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/#language-extension).


Summary
===

- Inductive types are fundamental to Lean (and Type Theory)
- Structures are inductive types with one constructor and many methods
- Products and sums record pairs and choices, respectively
- Π-types are generalizations of products, and are built in
- Σ-types are generalized choices, and are defined as structures
- Notation can be defined for _anything_ you want. Use with care.

These data types can be used to construct a large part of mathematics,
including algebra, topology, analysis, logic, computability, and so on.


Exercises
===

<ex/> Define a polymorphic tree type `MyTree` where every node may have any number of
children (using List). Define a few example trees demonstrating the features of your datatype.

<ex/> Define a method that maps a function onto the tree. Demonstrate
the method by mapping a function that squares it's argument onto
a tree made of natural numbers.

<ex/> Create a function that converts a `BTree` to a `MyTree`.
Test on your examples.

Exercises
===

<ex/> Consider the Dyadic Rationals, which consist of fractions who's
denominators are powers of two. We can define PreDyadics as follows.
We use the name `PreDyadic` elements in this type are not unique.
Later we will use this definition to define the Dyadic Rationals properly.



<div class="lean-code" data-start-line="833" data-end-line="839"><pre><code>namespace Temp

inductive PreDyadic where
  | zero    : PreDyadic
  | add_one : PreDyadic → PreDyadic  -- x ↦ x + 1
  | half    : PreDyadic → PreDyadic  -- x ↦ x / 2
  | neg     : PreDyadic → PreDyadic  -- x ↦ -x</code></pre></div>



a. Define `PreDyadic.double` that doubles a `PreDyadic`.<br>
b. Define `PreDyadic.add` that adds two `PreDyadic` values.<br>
c. Define `PreDyadic.mul` that multiplies two `PreDyadic` values.<br>
d. Define a function `PreDyadic.to_rat` that converts a `PreDyadic` to a `Rat`.<br>
e. Define the Dyadics `5/8` and `-7/32` and test your methods on these values.<br>
f. Are Dyadics as defined here unique? Why or why not?



<div class="lean-code" data-start-line="852" data-end-line="854"><pre><code>--hide
end Temp
--unhide</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

