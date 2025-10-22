import Mathlib

namespace LeanW26

/-
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
-/

end LeanW26
