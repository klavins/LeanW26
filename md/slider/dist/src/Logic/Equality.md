
Equality
===
... one should instead show that they are really equal by disclosing the inner ground for their equality
Emmy Noether, <a href="https://shethoughtit.ilcml.com/biography/emmy-noether/">She Thought It</a>.


Objects, Functions and Equality
===

We extend the first order logic to deal with functions of objects in our universe.
A critical components is a notion of **equality** between objects.

Astonishingly, Lean's equality is not a built in type, but is defined in the standard library.
Once we have equality, we can start working with statements
about functions and their relationships in earnest.

Equality is Defined Inductively
===

To lean how equality works, let's define our own version of it.


<div class="lean-code" data-start-line="38" data-end-line="46"><pre><code>universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl a : MyEq a a

#check MyEq 1 2

example : MyEq 1 1 :=
  MyEq.refl 1</code></pre></div>

 We can define notation 

<div class="lean-code" data-start-line="50" data-end-line="52"><pre><code>infix:50 &quot; ~ &quot;  =&gt; MyEq

#check 1 ~ 1</code></pre></div>


Refl is Powerful
===

Terms that are beta-reducible to each other are considered definitionally equal.
You can show many of equalities automatically 

<div class="lean-code" data-start-line="61" data-end-line="62"><pre><code>example : 1 ~ 1 :=
  MyEq.refl 1</code></pre></div>

 The `apply` tactic figures out what the argument to `refl` should be. 

<div class="lean-code" data-start-line="66" data-end-line="70"><pre><code>example : 2 ~ (1+1) := by
  apply MyEq.refl

example : 9 ~ (3*(2+1)) := by
  apply MyEq.refl</code></pre></div>


These proofs do not use rules of arithmetic like associativity.
They use proof by computation (reducibility). So
```lean
| refl a : MyEq a a
```
works for any two definitionally equivalent forms of `a`.



Substitution
===

Substitution is the second most critical property of the equality.
It allows us to conclude, for example, that if `x = y` and `p x` then `p y`. 

<div class="lean-code" data-start-line="89" data-end-line="92"><pre><code>theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
                   (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁ with
  | refl =&gt; exact h₂</code></pre></div>

 The cases tactic compiles a term that uses the recursor for `MyEq`.

**Example:** Here is an example where we substitute `y` for `x`
to prove equality between two propositions. 

<div class="lean-code" data-start-line="99" data-end-line="102"><pre><code>example {x y : Nat} : x ~ y → (x &gt; 2 ↔ y &gt; 2) := by
  intro h
  apply MyEq.subst h       -- goal becomes x &gt; 2 ↔ x &gt; 2
  exact ⟨ id, id ⟩</code></pre></div>


Symmetry and Transitivity
===
You can use substitution to show the standard properties we know and love about equality. 

<div class="lean-code" data-start-line="110" data-end-line="117"><pre><code>theorem MyEq.sym {α : Sort u} {a b : α} : a ~ b → b ~ a := by
  intro h
  apply MyEq.subst h
  exact MyEq.refl a

theorem MyEq.trans {α : Sort u} {a b c : α} : a ~ b → b ~ c → a ~ c := by
  intro hab hbc
  exact MyEq.subst hbc hab</code></pre></div>

 Here is an example showing the use of both of these theorems at once. 

<div class="lean-code" data-start-line="121" data-end-line="123"><pre><code>example {x y z : Nat} : y ~ x → z ~ y → x ~ z := by
  intro h1 h2
  apply MyEq.trans (MyEq.sym h1) (MyEq.sym h2)</code></pre></div>


Congruence
===

Congruence is critical for equation solving.


<div class="lean-code" data-start-line="132" data-end-line="135"><pre><code>theorem MyEq.congr_arg {α : Sort u} {a b : α} {f : α → α} : a ~ b → f a ~ f b := by
  intro hab
  apply MyEq.subst hab
  exact MyEq.refl (f a)</code></pre></div>

 For example, 

<div class="lean-code" data-start-line="140" data-end-line="141"><pre><code>example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 :=
  fun h =&gt; MyEq.congr_arg (f := fun w =&gt; 2*w + 1) h</code></pre></div>

 Or, with tactics 

<div class="lean-code" data-start-line="145" data-end-line="148"><pre><code>example (x y : Nat) : x ~ y → 2*x+1 ~ 2*y + 1 := by
  intro h
  apply MyEq.congr_arg (f := fun w =&gt; 2*w + 1)    -- goal becomes x ~ y
  exact h</code></pre></div>


Lean's Equality
===

Lean's equality relation is called `Eq` and its notation is `=`,
as we have been using. Lean also defines `rfl` to be `Eq.refl _` 

<div class="lean-code" data-start-line="157" data-end-line="159"><pre><code>#print rfl
example : 9 = 3*(2+1) := Eq.refl 9
example : 9 = 3*(2+1) := rfl</code></pre></div>

 Lean provides a long list of theorems about equality, such as 

<div class="lean-code" data-start-line="163" data-end-line="172"><pre><code>#check Eq.symm            -- a = b → b = a
#check Eq.subst           -- a = b → motive a → motive b
#check Eq.substr          -- b = a → p a → p b
#check Eq.trans           -- a = b → b = c → a = c
#check Eq.to_iff          -- a = b → (a ↔ b) when a and b are Prop
#check Eq.mp              -- α = β → α → β
#check Eq.mpr             -- α = β → β → α
#check congrArg           -- (f : α → β), a₁ = a₂ → f a₁ = f a₂
#check congrFun           -- f = g → ∀ (a : α), f a = g a
#check congr              -- (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂</code></pre></div>


The Triangle Macro
===

`h ▸ e` is a macro built on top of `Eq.rec` and `Eq.symm` definitions.

Given `h : a = b` and `e : p a`, the term `h ▸ e` has type `p b`.

`h ▸ e` is like a "type casting" operation where you change the type of `e` by using `h`.

For example:



<div class="lean-code" data-start-line="189" data-end-line="190"><pre><code>example (α : Type) (a b : α) (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b :=
  h₁ ▸ h₂</code></pre></div>

 A nice example is how `Eq.symm` is proved: 

<div class="lean-code" data-start-line="194" data-end-line="194"><pre><code>example (a b : Type) (h : a = b) : b = a := h ▸ rfl</code></pre></div>

 Or `Eq.trans`: 

<div class="lean-code" data-start-line="198" data-end-line="199"><pre><code>theorem Eq.trans {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
  h₂ ▸ h₁</code></pre></div>


Exercises
===

<ex /> Prove the `to_iff` theorem for `MyEq`. Hint, study the proof for `MyEq.subst`.



<div class="lean-code" data-start-line="209" data-end-line="209"><pre><code>theorem MyEq.to_iff (a b : Prop) : a ~ b → (a ↔ b) := sorry</code></pre></div>


<ex /> Try finding a use for `▸` in a proof of:



<div class="lean-code" data-start-line="216" data-end-line="216"><pre><code>example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z := sorry</code></pre></div>


Rewriting
===

 `rw[h]`: Rewrites the current goal using the equality h. 

<div class="lean-code" data-start-line="225" data-end-line="227"><pre><code>theorem t1 (a b : Nat) : a = b → a + 1 = b + 1 := by
  intro hab
  rw[hab]</code></pre></div>

 The `rw` tactic is doing a searching for pattern matches and then using
the basic theorems about equality. 

<div class="lean-code" data-start-line="232" data-end-line="234"><pre><code>#print t1      -- theorem LeanW26.t1 : ∀ (a b : ℕ), a = b → a + 1 = b + 1 :=
               -- fun a b hab ↦ Eq.mpr (id (congrArg (fun _a ↦ _a + 1 = b + 1)
               -- hab)) (Eq.refl (b + 1))</code></pre></div>


More Rewriting
===

 To use an equality backwards, use ← (written \left)

<div class="lean-code" data-start-line="242" data-end-line="244"><pre><code>theorem t2 (a b c : Nat) : a = b ∧ a = c → b + 1 = c + 1 := by
  intro ⟨ h1, h2 ⟩
  rw[←h1, ←h2]</code></pre></div>

 You can also rewrite assumptions using `at`. 

<div class="lean-code" data-start-line="248" data-end-line="251"><pre><code>example (a b c : Nat) : a = b → a = c → b + 1 = c + 1 := by
  intro h1 h2
  rw[h1] at h2
  rw[h2]</code></pre></div>

 Rewrite variants include 

<div class="lean-code" data-start-line="255" data-end-line="256"><pre><code>#help tactic rewrite          -- rewrite without rfl at the end
#help tactic nth_rewrite      -- rewrite a specific sub-term</code></pre></div>


The Simplifier
===

 The simplifier uses equations and lemmas to simplify expressions 

<div class="lean-code" data-start-line="266" data-end-line="267"><pre><code>theorem t3 (a b : Nat) : a = b → a + 1 = b + 1 := by
  simp</code></pre></div>

 Sometimes you have to tell the simplifer what equations to use. 

<div class="lean-code" data-start-line="271" data-end-line="279"><pre><code>theorem t4 (a b c d e : Nat)
 (h1 : a = b)
 (h2 : b = c + 1)
 (h3 : c = d)
 (h4 : e = 1 + d)
 : a = e := by
    simp[h1,h2,h3,h4,Nat.add_comm]          -- simp[*] also works

#check Nat.add_comm       -- Try Loogle &quot;Nat&quot; for more</code></pre></div>

 `simp` has many variants: `simp?`, `simp at`, `simp_all`, `dsimp`, `simpa`, `field_simp`, ... 

Adding Theorems to the Simplifier
===

Any theorem of the form `x=y` or `p↔q` can be added to the simplifier. To avoid
loops, it is usually best to have the left hand side be more complicated than the
right hand side.


<div class="lean-code" data-start-line="293" data-end-line="300"><pre><code>inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
  | up =&gt; dn
  | dn =&gt; up

postfix:95 &quot; ⁻¹ &quot; =&gt; toggle</code></pre></div>

 Let's add some basic theorems to the simplifier. 

<div class="lean-code" data-start-line="304" data-end-line="305"><pre><code>@[simp] theorem toggle_up : up⁻¹ = dn := rfl
@[simp] theorem toggle_dn : dn⁻¹ = up := rfl</code></pre></div>


Using Spin's simps
===

 We can use these theorems to prove another theorem, which is also added to
the simplifier. 

<div class="lean-code" data-start-line="315" data-end-line="316"><pre><code>@[simp] theorem toggle_toggle {x} : x⁻¹⁻¹ = x := by
  cases x &lt;;&gt; simp?  -- uses toggle_up, toggle_dn</code></pre></div>

 And then prove yet another theorem. 

<div class="lean-code" data-start-line="320" data-end-line="320"><pre><code>example {x} : x⁻¹⁻¹⁻¹ = x⁻¹ := by simp -- uses toggle_toggle</code></pre></div>


Adding more simps
===


<div class="lean-code" data-start-line="327" data-end-line="332"><pre><code>def op (x y : Spin) : Spin := match x, y with
  | up,dn =&gt; dn
  | dn,up =&gt; dn
  | _,_ =&gt; up

infix:75 &quot; o &quot; =&gt; op</code></pre></div>

 And some simplifications: 

<div class="lean-code" data-start-line="336" data-end-line="339"><pre><code>@[simp] theorem op_up_left {x}  : up o x = x := by cases x &lt;;&gt; rfl
@[simp] theorem op_up_right {x} : x o up = x := by cases x &lt;;&gt; rfl
@[simp] theorem op_dn_left {x}  : dn o x = x⁻¹ := by cases x &lt;;&gt; rfl
@[simp] theorem op_dn_right {x} : x o dn = x⁻¹ := by cases x &lt;;&gt; rfl</code></pre></div>

 Using these, we can show: 

<div class="lean-code" data-start-line="343" data-end-line="345"><pre><code>@[simp] theorem toggle_op_left {x y} : (x o y)⁻¹ = x⁻¹ o y := by
  cases x &lt;;&gt; simp   -- case 1 uses op_up_left, toggle_up, op_dn_left
                     -- case w uses op_dn_left, toggle_toggle, toggle_dn, op_up_left</code></pre></div>


Exercise
===

<ex /> Prove the following using `rw` and `simp`. When you do use `simp`,
make a note of which theorems it is calling for each case (using `simp?`).



<div class="lean-code" data-start-line="356" data-end-line="366"><pre><code>theorem assoc {x y z} : x o (y o z) = (x o y) o z := sorry

theorem com {x y} : x o y = y o x := sorry

theorem toggle_op_right {x y} : (x o y)⁻¹ = y o x⁻¹ := sorry

@[simp]
theorem inv_cancel_right {x} : x o x⁻¹ = dn := sorry

@[simp]
theorem inv_cancel_left {x} : x⁻¹ o x = dn := sorry</code></pre></div>


The `linarith` Tactic
===

The `linarith` tactic attempts to solve linear equalities and
inequalities and works on `ℕ`, `ℤ`, `ℚ`, `ℝ` and related types.

On `ℕ` and `ℤ` it is incomplete, but on `ℚ` and `ℝ` it is complete.



<div class="lean-code" data-start-line="380" data-end-line="391"><pre><code>example (a b c d e : Nat)
 (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d)
 : a = e := by
 linarith

example (x y z : ℚ) (h1 : 2*x - y + 3*z = 9)
                    (h2 : x - 3*y - 2*z = 0)
                    (h3 : 3*x + 2*y -z = -1)
 : x = 1 ∧ y = -1 ∧ z = 2 := by
 constructor
 · linarith
 · constructor &lt;;&gt; linarith</code></pre></div>


Example : Induction on Nat
===

As an example the brings many of these ideas together, consider
the sum of the first `n` natural numbers, which is `n(n+1)/2`.


<div class="lean-code" data-start-line="402" data-end-line="412"><pre><code>def S (n : Nat) : Nat := match n with
  | Nat.zero =&gt; 0
  | Nat.succ x =&gt; n + S x

example : ∀ n, 2 * S n = n*(n+1) := by
  intro n
  induction n with
  | zero =&gt; simp[S]
  | succ k ih =&gt;
    simp[S]
    linarith         -- uses ih (check with clear ih before linarith)</code></pre></div>


Exercise
===

<ex /> Let



<div class="lean-code" data-start-line="422" data-end-line="424"><pre><code>def T (n : Nat) : Nat := match n with
  | Nat.zero =&gt; 0
  | Nat.succ x =&gt; n*n + T x</code></pre></div>


Show the following using the `induction` tactic:


<div class="lean-code" data-start-line="430" data-end-line="430"><pre><code>example (n : Nat) : 6 * (T n) = n * (n+1) * (2*n+1) :=  sorry</code></pre></div>


Inequality
===

Any two elements of an inductive type constructed differently are not equal. 

<div class="lean-code" data-start-line="439" data-end-line="441"><pre><code>example : up ≠ dn := by
  intro h
  exact Spin.noConfusion h</code></pre></div>


Confused about noConfusion?
===

`Thing.noConfusion` is a `theorem` built from `Thing.noConfusionType`.
We could redefine something like it as follows: 

<div class="lean-code" data-start-line="450" data-end-line="465"><pre><code>def nc_type (P : Prop) (x y : Spin) : Prop :=
  match x, y with
  | up, up =&gt; P
  | up, dn =&gt; False
  | dn, up =&gt; False
  | dn, dn =&gt; P

example : nc_type True up up = True  := by rfl
example : nc_type True dn up = False := by rfl

example : up ≠ dn := by
  intro h
  have hAB : nc_type True up dn := by
    rw[←h]                              -- ⊢ nc_type True A A
    trivial
  exact hAB                             -- nc_type True A B is equivalent to False</code></pre></div>


Other Ways to Show Inequality
===


<div class="lean-code" data-start-line="473" data-end-line="480"><pre><code>example : up ≠ dn := by
  intro h
  cases h     -- uses Eq.casesOn, Thing.ctorIdx, and Nat.noConfusion

example : up ≠ dn := by
  intro h
  have : Spin.ctorIdx up = Spin.ctorIdx dn := by rw[h]
  exact Nat.noConfusion this</code></pre></div>

 Or you can use nomatch on `h`. 

<div class="lean-code" data-start-line="484" data-end-line="486"><pre><code>example : up ≠ dn := by
  intro h
  nomatch h</code></pre></div>

 Which is the same as 

<div class="lean-code" data-start-line="490" data-end-line="490"><pre><code>example : up ≠ dn := fun h =&gt; match h with .     -- marked as deprecated</code></pre></div>

 All of these methods work with other inductive types like `Nat` and `PreDyadic` as well. 

Reasoning using noConfusion
===

Continuing the above example, suppose we want to specify who is on who's right side. 

<div class="lean-code" data-start-line="501" data-end-line="516"><pre><code>inductive Person where | mary | steve | ed | jolin
open Person

def on_right (p : Person) := match p with
  | mary =&gt; steve
  | steve =&gt; ed
  | ed =&gt; jolin
  | jolin =&gt; mary

def next_to (p q : Person) := on_right p = q ∨ on_right q = p

example : ¬next_to mary ed := by
  intro h
  cases h with
  | inl hme =&gt; exact noConfusion hme
  | inr hem =&gt; exact noConfusion hem</code></pre></div>


Trivial
===

The `trivial` tactic (not to be confused with the `trivial` theorem),
sometimes figures out when to apply `noConfusion` 

<div class="lean-code" data-start-line="525" data-end-line="529"><pre><code>theorem t10 : ed ≠ steve := by
  intro h
  trivial

#print t10       -- fun h ↦ False.elim (noConfusion_of_Nat Person.ctorIdx h)</code></pre></div>


Exercises
===

<ex /> For `PreDyadic`, show
```lean
example (x : PreDyadic) : zero ≠ add_one x

example : ¬zero.add_one = zero.add_one.add_one.half := sorry
```
using `noConfusion`.

<ex /> Show
```lean
example (x y : PreDyadic) : add_one x = add_one y ↔ x = y := sorry
```



Equality for Structure Types
===

Two terms of a structure type are equal if the values of their fields
are equal.

For example, given



<div class="lean-code" data-start-line="563" data-end-line="565"><pre><code>structure Point (α : Type u) where
  x : α
  y : α</code></pre></div>

 We can show 

<div class="lean-code" data-start-line="569" data-end-line="573"><pre><code>theorem Point.ext {α : Type} (p q : Point α) (hx : p.x = q.x) (hy : p.y = q.y)
  : p = q := by
  cases p with | mk a b =&gt;
  cases q with | mk c d =&gt;
  simp_all</code></pre></div>

 Then we can do, for example, 

<div class="lean-code" data-start-line="577" data-end-line="580"><pre><code>example (x y : Nat) : Point.mk (x+y) (x+y) = Point.mk (y+x) (y+x) := by
  apply Point.ext
  · exact add_comm x y
  · exact add_comm x y</code></pre></div>


Defining Extensionality Automatically
===

If we add the @[ext] tag to a definition, we can automatically
define extensionality and register it to be used with the `ext` tactic.


<div class="lean-code" data-start-line="590" data-end-line="598"><pre><code>@[ext]
structure Komplex where
  re : ℝ
  im : ℝ

example (x y : ℝ) : Komplex.mk (x+y) (x+y) = Komplex.mk (y+x) (y+x) := by
  ext
  · exact add_comm x y
  · exact add_comm x y</code></pre></div>


Function Extensionality
===

Two functions are considered equal if they assign the same value to every
argument. The theorem that allows us to prove that is 

<div class="lean-code" data-start-line="607" data-end-line="607"><pre><code>#check funext -- (∀ (x : α), f x = g x) → f = g</code></pre></div>

 Here is an example: 

<div class="lean-code" data-start-line="611" data-end-line="617"><pre><code>def f (n : ℕ) := n + 1
def g (n : ℕ) := 1 + n

example : f = g := by
  funext x
  unfold f g              -- not needed, but makes it easy to see the goal
  rw[add_comm]</code></pre></div>


<div class='fn'>In some languages, function extensionality is an axiom.
In Lean, it follows from the properties of quotients (which we will get in to
later). This approach was possibly first described in
<a href="https://ncatlab.org/nlab/files/HofmannExtensionalIntensionalTypeTheory.pdf">Extensional concepts in intensional type theory</a> by Martin Hoffman. </div>


Example : Shift
===

Suppose we define


<div class="lean-code" data-start-line="632" data-end-line="632"><pre><code>def shift (k x : ℤ) : ℤ := x+k</code></pre></div>

 Then we can show 

<div class="lean-code" data-start-line="636" data-end-line="644"><pre><code>@[simp]
theorem shift_inv_right {k} : shift k ∘ shift (-k) = id := by
  funext x              -- x : ℤ ⊢ (shift k ∘ shift (-k)) x = id x
  simp[shift]

@[simp]
theorem shift_inv_left {k} : shift (-k) ∘ shift k = id := by
  funext x
  simp[shift]</code></pre></div>


Shift is a Bijection
===

Lean's standard library provides a number of theorems about functions in the Function library.


<div class="lean-code" data-start-line="653" data-end-line="658"><pre><code>open Function

#print Bijective                    -- fun {α} {β} f ↦ Injective f ∧ Surjective f
#check bijective_iff_has_inverse    -- Bijective f ↔ ∃ g, LeftInverse g f ∧ RightInverse g f
#check leftInverse_iff_comp         -- LeftInverse f g ↔ f ∘ g = id
#check rightInverse_iff_comp        -- RightInverse f g ↔ g ∘ f = id</code></pre></div>

 and more. Use Loogle to look up `Function`.

Using the above, we can show:


<div class="lean-code" data-start-line="665" data-end-line="670"><pre><code>example {k} : Bijective (shift k) := by
  rw[bijective_iff_has_inverse]
  use shift (-k)
  constructor
  · simp[leftInverse_iff_comp]     -- uses shift_inv_left
  · simp[rightInverse_iff_comp]    -- uses shift_inv_right</code></pre></div>


Exercises
===

<ex /> Instead of `shift_inv_left` and `shift_inv_right` as simplifiers, we could have used



<div class="lean-code" data-start-line="680" data-end-line="681"><pre><code>@[simp] theorem shift_zero : shift 0 = id := sorry
@[simp] theorem shift_add {j k} : shift k ∘ shift j = shift (j+k) := sorry</code></pre></div>



Prove these two theorems and show that the proof of `example {k} : Bijective (shift k)` still
goes through, but with the simplifier using `shift_zero` and `shift_add`.

Note: If `shift_inv_left` and `shift_inv_right` are still registered as simps, you can use 

<div class="lean-code" data-start-line="690" data-end-line="691"><pre><code>attribute [-simp] shift_inv_left
attribute [-simp] shift_inv_right</code></pre></div>



<ex /> For `PreDyadic` show
```lean
example : double ∘ half = id := sorry
```





Equiv
===

`Equiv` is a structure defined in [Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Defs.html) for showing equivalences between types.
It is defined:

```lean
structure Equiv (α : Sort u_1) (β : Sort u_2) : Sort (max (max 1 u_1) u_2)
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse self.invFun self.toFun
  right_inv : RightInverse self.invFun self.toFun
```

The notation `X ≃ Y` is is used to represent the equivalence and
the library supports the following notation:



<div class="lean-code" data-start-line="725" data-end-line="729"><pre><code>variable (X Y : Type) (x : X) (y : Y)
variable (e : X ≃ Y)

#check e x         -- preferred way to write e.toFun x
#check e.symm y    -- preferred way to write e.invFun y</code></pre></div>

 `Equiv` and its extensiosn are used heavily in Mathlib.  

Example : Natural ≃ Nats
===

Recall we defined an alternative natural number type with:


<div class="lean-code" data-start-line="740" data-end-line="753"><pre><code>mutual
  inductive Ev
  | zero : Ev
  | succ : Od → Ev
  deriving Repr              -- allows Lean to print Ev terms

  inductive Od
  | succ : Ev → Od
  deriving Repr              -- allows Lean to print Od terms
end

def Natural := Ev ⊕ Od

namespace Natural</code></pre></div>


Our goal is to define an equivalnce showing
```lean
Natural ≃ Nat
```


Converting Natural to Nat
===

We first define an `of_nat` function converting a `Nat` to a `Natural`.



<div class="lean-code" data-start-line="770" data-end-line="783"><pre><code>def zero : Natural := .inl Ev.zero

def succ (x : Natural) : Natural := match x with
  | .inl a =&gt; .inr (Od.succ a)
  | .inr a =&gt; .inl (Ev.succ a)

def of_nat (n : Nat) : Natural := match n with
  | Nat.zero =&gt; .zero
  | Nat.succ k =&gt; .succ (of_nat k)

#eval Natural.of_nat 3    -- Sum.inr (Od.succ (Ev.succ (Od.succ (Ev.zero))))

instance : Zero Natural := ⟨ .zero ⟩
instance : One Natural := ⟨ .succ .zero ⟩</code></pre></div>


Converting Natural to Nats
===

Next we define a `to_nat` function convering `Natural` to `Nat`.

 

<div class="lean-code" data-start-line="794" data-end-line="808"><pre><code>mutual
  def Ev.to_nat : Ev → Nat
    | .zero =&gt; 0
    | .succ k =&gt; .succ (Od.to_nat k)
  def Od.to_nat : Od → Nat
    | .succ k =&gt; .succ (Ev.to_nat k)
end

def to_nat (n : Natural) : Nat := match n with
  | .inl k =&gt; Ev.to_nat k
  | .inr k =&gt; Od.to_nat k

#eval to_nat (of_nat 16) -- 16

#eval of_nat (to_nat (of_nat 3))  -- Sum.inr (Od.succ (Ev.succ (Od.succ (Ev.zero))))</code></pre></div>


Left Inverse
===

To build out the equivalence, we first show that `of_nat` is a left inverse of `to_nat`.

By the way, theorems can be *mutually defined*!



<div class="lean-code" data-start-line="820" data-end-line="835"><pre><code>mutual

  @[simp]
  theorem Ev.left_inv {ev : Ev} : of_nat (Ev.to_nat ev) = Sum.inl ev := by
    cases ev &lt;;&gt; simp[Ev.to_nat,of_nat,succ,Od.left_inv,zero]

  @[simp]
  theorem Od.left_inv {od : Od} : Natural.of_nat (Od.to_nat od) = Sum.inr od := by
    cases od; simp[Od.to_nat,of_nat,succ,Ev.left_inv]

end

theorem left_inv {n : Natural} : Natural.of_nat n.to_nat = n := by
    cases n with
    | inl _ =&gt; exact Ev.left_inv
    | inr _ =&gt; exact Od.left_inv</code></pre></div>


Right Inverse
===

Next we show `to_nat` is a right inverse of `of_nat`.



<div class="lean-code" data-start-line="845" data-end-line="859"><pre><code>@[simp]
theorem to_nat_succ {m : Natural}
  : m.succ.to_nat = m.to_nat.succ := by
  cases m &lt;;&gt; aesop

@[simp]
theorem right_inv {n : Nat} : (Natural.of_nat n).to_nat = n := by
  induction n with
    | zero =&gt; aesop
    | succ n ih =&gt;
      unfold Natural.of_nat -- common pattern in induction. required for ih to apply.
      conv =&gt;
        rhs
        rw[←ih]
      rw[to_nat_succ]</code></pre></div>


The Equivalence
===

Finally we have the desired equivalence.


<div class="lean-code" data-start-line="869" data-end-line="874"><pre><code>def equiv_nat : Natural ≃ Nat:= {
  toFun := Natural.to_nat,
  invFun := Natural.of_nat,
  left_inv _ := left_inv,
  right_inv _ := right_inv
}</code></pre></div>

 Here's an example of transporting addition and multiplication from `Nat` to `Natural`.  

<div class="lean-code" data-start-line="878" data-end-line="885"><pre><code>instance add : Add Natural := equiv_nat.add
instance mul : Mul Natural := equiv_nat.mul

def three := of_nat 3
def twelve := of_nat 12
def thirteen := of_nat 13

#eval to_nat (three * ( twelve + thirteen ) )     -- 75</code></pre></div>


Exercise
===

<ex /> Show



<div class="lean-code" data-start-line="896" data-end-line="896"><pre><code>def spin_bool_equiv : Spin ≃ Bool := sorry</code></pre></div>


Exercise
===

<ex /> (Optional) Consider the following two types for the complex numbers.



<div class="lean-code" data-start-line="906" data-end-line="915"><pre><code>structure K1 where
  re : ℝ
  im : ℝ

structure K2 where
  a : ℝ
  θ : ℝ
  pa := 0 ≤ a
  pθ := 0 ≤ θ ∧ θ &lt; 2*Real.pi
  h : a = 0 → θ = 0</code></pre></div>

 Define the natural equivalence  

<div class="lean-code" data-start-line="919" data-end-line="924"><pre><code>def K_equiv : K1 ≃ K2 := sorry

--hide
end Natural
end LeanW26
--unhide</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

