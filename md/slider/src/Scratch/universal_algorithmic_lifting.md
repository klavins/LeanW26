
<div class="lean-code" data-start-line="1" data-end-line="15"><pre><code>def dumb_max (x y : Nat) :=
  let x&#x27; := x + 10000000000000
  let y&#x27; := y + 10000000000000
  max x&#x27; y&#x27; - 10000000000000

example : dumb_max 5 10 = 10 := rfl

theorem max_eq {a b : Nat} : max a b = dumb_max a b := by
  simp[dumb_max]

#print max_eq

example : dumb_max 5 10 = 10 := by
  dumb_max_tactic
  sorry</code></pre></div>


License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

