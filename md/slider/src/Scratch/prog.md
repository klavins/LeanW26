
<div class="lean-code" data-start-line="1" data-end-line="51"><pre><code>import mathlib

namespace LeanW26

def insert (x : ℕ) : List ℕ → List ℕ
| [] =&gt; [x]
| y :: ys =&gt; if  x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort :  List ℕ → List ℕ
| [] =&gt; []
| x :: xs =&gt; insert x (insertionSort xs)

#eval insertionSort [1,4,6,5,2]

end LeanW26

namespace LeanW26&#x27;

def insert {A : Type} (lt : A → A → Bool) (x : A) : List A → List A
| [] =&gt; [x]
| y :: ys =&gt; if lt x y then x :: y :: ys else y :: insert lt x ys

def insertionSort {A : Type} (lt : A → A → Bool) (L : List A) : List A :=
match L with
| [] =&gt; []
| x :: xs =&gt; insert lt x (insertionSort lt xs)

#eval  (· + ·) 1 2

#eval insertionSort (· ≤ ·) [1,4,6,5,2]

#eval insertionSort (· ≤ ·) [&quot;a&quot;, &quot;hello&quot;, &quot;goodbye&quot;, &quot;000&quot;]

#eval &#x27;a&#x27; ≤ &#x27;b&#x27;
#eval insertionSort (· ≤ ·) [&#x27;a&#x27;,&#x27;b&#x27;,&#x27;b&#x27;]

#eval [10,2,3] ≤ [3,4,5]


end LeanW26&#x27;

inductive MyList {A : Type} where
  | nil : MyList
  | cons : A → MyList → MyList

#eval &quot;asd&quot;.toList

#eval String.ofList [&#x27;2&#x27;]

def c := &#x27;1&#x27;
#eval String.ofList [c] ++ &quot;34&quot;</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

