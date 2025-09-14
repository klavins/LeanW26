
<div style='display:none'>
--  Copyright (C) 2025  Eric Klavins
--
--  This program is free software: you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation, either version 3 of the License, or
--  (at your option) any later version.   
</div>

<span style='color: orange'>***UNDER CONSTRUCTION***</span><br>
<span style='color: lightgray; font-size: 10pt'><a href='https://github.com/klavins/LeanBook/blob/main/main/../LeanBook/Chapters/Integers/Intro.lean'>Code</a> for this chapter</span>
 # Integers via Quotients

Now that we have defined the natural numbers `Nat`, the next obvious step is to define the integers `Int`, which included positive _and_negative whole numbers. This can be done in several ways. For example, the Lean 4 standard library defines integers inductively saying that (a) any natural number is an integer, and (b) the negative successor of an integer is an integer.

Here, mainly to synergystically illustrate the use of **quotients**, we take a different approach, which is standard in foundational mathematics, although perhaps not as idiomatically type theoretic. We define pairs of natural numbers `(p,q)` and use the convention that if `p>q` then `(p,q)` represents the positive number `p-q`. Otherwise, it represents the non-positive number `q-p`.

This construction allows for multiple representatives of the same number. Therefore, we define an equivalence `≈` on pairs. We would like to write `(p,q) ≈ (r,s)` if and only if `p-q=r-s`, but since we are in the process of defining the integers, we do not yet have a notion of negative numbers. Some rearrangement leads to
```
(p,q) ≈ (r,s)  ↔   p+s=q+r
```
instead.

With this equivalence in place, we define an integer to be the equivalence class corresponding to a given difference. For example,
```
-2 ≡ { (0,2), (1,3), (2,4), ... }
```

Although we could define -2 to be the _set_ of such pairs, Lean has a much more powerful tool for such constructions: the quotient. Taking the quotient of the set of pairs with respect to the equivalence relation we have defined allows us to use _definitional equality_ on equivalence classes of pairs. This allows us, for example, to substitute an integer for an equivalent one in an algebreic expression.

 

<div style='height=50px'>&nbsp;</div><hr>
Copyright © 2025 Eric Klavins
