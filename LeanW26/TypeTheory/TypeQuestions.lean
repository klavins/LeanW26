/-
Type Theory Questions
===

**TYPE CHECKING**: In a given context, does a term M have a given type σ?
```lean
Γ ⊢ M : σ
```

**WELL TYPEDNESS**: Does there exist a context in which a type be assigned to a
term M? Another way of saying this is "is M a legal term?"
```lean
? ⊢ M : ?
```

**TYPE INFERENCE**: Can M be assigned a type consistent with a given context?
```lean
Γ ⊢ M : ?
```

**INHABITATION**: Does there exist a term of a given type? If σ is a logical
statement, then this is the question of whether σ has a proof.
```lean
Γ ⊢ ? : σ
```
-/
