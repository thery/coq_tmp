---
by: lia
---

# sqrt_sq_md

Let `a b : Z`. If `0 <= a` and `0 <= b` then `0 <= Z.sqrt a * Z.sqrt a + Z.sqrt b`.

- We have `0 <= Z.sqrt a` and `0 <= Z.sqrt b`.
- So `0 <= Z.sqrt a * Z.sqrt a`.
  - It suffices to prove `0 <= Z.sqrt a`.
