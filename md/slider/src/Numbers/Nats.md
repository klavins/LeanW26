
Natural Numbers
===

Algebraic Structure of ℕ
===

Commutative monoid under addition
- Associativity: `(a+b)+c = a+(b+c)`
- Commutativity: `a+b  =b+a`
- Identity element: `0+a = a`

Commutative monoid under multiplication
- Associativity: `(a*b)*c = a*(b*c)`
- Commutativity: `a*b = b*a`
- Identity element: `0*a = a`

Commutative semiring
- Left Distributivity: `a*(b+c) = a*b+a*c`
- Right Distributivity: `(a+b)*c = a*c+b*c`
- Zero rule: `0*a = 0`

No zero divisors
- If `a*b=0` then `a=0` or `b=0`


```lean
example {x : ℕ} : x + 0 = x := by
  rw[Nat.add_comm]
  rw[Nat.zero_add]


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

