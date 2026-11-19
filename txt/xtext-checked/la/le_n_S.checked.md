---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ Sint `n m : nat`{.var}. Ponamus `n <= m`{.hyp} (H). Ostendamus `S n <= S m`{.claim}.

- ▫️ Ostendamus `S n <= S m`{.fact} per inductionem in `n <= m`{.fact} (H) (le, le_ind):
- ✅ Casus 1 (basis): ostendamus `S n <= S n`{.claim}.
  - ✅ Ex definitione le (le_n), habemus `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- ✅ Casus 2 (gradus): ostendamus `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - ▫️ Eligamus quaelibet `m0 : nat`{.var}; ponamus `n <= m0`{.hyp} (H0) et per hypothesim inductionis `S n <= S m0`{.hyp} (IH).
    - ✅ Ex definitione le (le_S) cum teste `S m0`{.fact}, ex `S n <= S m0`{.fact} (IH) unde sequitur `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- ✅ Habemus `S n <= S m`{.claim} in omnibus casibus.
