---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# errors_file

Let `a b : Z`{.var}. Assume `0 < a < b`{.hyp} (h). We prove `a * a < b * b`{.claim}.

- By *sqrt_magic*{.just} we have `0 < a`{.claim}.
- We have `0 < b - a`{.clam} and so `0 < b - a`{.claim}.
- Assume `a = b`{.hyp} (k).
  - Then `a * a = b * b`{.claim} by *k*{.just}.
- [We have `0 < b`{.claim} by *h*{.just}.
- Also `0 < a +`{.claim}.
- Hence `a * a < b * b`{.claim}.
