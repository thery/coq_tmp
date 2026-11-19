---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ Laat `n m : nat`{.var}. Stel `n <= m`{.hyp} (H). We bewijzen `S n <= S m`{.claim}.

- ▫️ We bewijzen `S n <= S m`{.fact} met inductie naar `n <= m`{.fact} (H) (le, le_ind):
- ✅ Geval 1 (basis): we bewijzen `S n <= S n`{.claim}.
  - ✅ Volgens de definitie van le (le_n), er geldt `S n <= S n`{.claim} *by Corelib.Init.Peano.le_n*.
- ✅ Geval 2 (inductief): we bewijzen `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - ▫️ Kies willekeurig `m0 : nat`{.var}; stel `n <= m0`{.hyp} (H0) en volgens de inductiehypothese `S n <= S m0`{.hyp} (IH).
    - ✅ Volgens de definitie van le (le_S) met getuige `S m0`{.fact}, uit `S n <= S m0`{.fact} (IH) hieruit volgt `S n <= S (S m0)`{.claim} *by Corelib.Init.Peano.le_S*.
- ✅ Er geldt `S n <= S m`{.claim} in alle gevallen.
