
Todo
===

    - Prop   := Sort 0
    - Type u := Sort (u+1)
    - Prop : Type 0 : Type 1 : Type 2 : ...
    - Allows Types do depend on Types
    - Can have type and univerrse polymorphism

    - Impredicative:
    ```∀ P : Prop, P → P``` ok. So you can define And (p : Prop) (q: Prop) : Prop
    ```∀ T : Type u, T → T : Type (u + 1)``` requires universe levels
    - Proof irrelevant: if hp : p and hq : p then hp = hq (And would be possible
      but awkward without impredicativity)


Todo
===

```lean
end LeanW26
```

License
===

Copyright (C) 2025  Eric Klavins

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.   

