---
require: From Stdlib Require Import Lia.
by: lia
---

# square_small

Let `n : nat`{.var}. Assume `n = 0 \/ n = 1`{.hyp} (h). We prove `n * n = n`{.claim}.

- By case analysis (*match*{.just}) on *h*{.just}, of type *or*{.just}:
  - If `n = 0`{.hyp} (h0), then by *h0*{.just} we have `n * n = n`{.claim}.
  - If `n = 1`{.hyp} (h1), then by *h1*{.just} we have `n * n = n`{.claim}.

  In both cases, `n * n = n`{.claim}.
