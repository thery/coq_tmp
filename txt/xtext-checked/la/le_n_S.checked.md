---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ Sint `n m : nat`{.var}. Ponamus `n <= m`{.hyp} (H). Ostendamus `S n <= S m`{.claim}.

- ✅ Ostendamus `S n <= S m` per inductionem in *H*{.just} (le, le_ind):
  - ✅ Casus 1 (basis): ostendamus `S n <= S n`{.claim}.
    - ✅ Ex definitione le (*le_n*{.just}), habemus `S n <= S n`{.claim}.
  - ✅ Casus 2 (gradus): ostendamus `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - ✅ Eligamus quaelibet `m0 : nat`{.var}; ponamus `n <= m0`{.hyp} (H0) et per hypothesim inductionis `S n <= S m0`{.hyp} (IH). Ex definitione le (*le_S*{.just}) cum teste `S m0`, ex *IH*{.just} unde sequitur `S n <= S (S m0)`{.claim}.

  Habemus `S n <= S m`{.claim} in omnibus casibus.
