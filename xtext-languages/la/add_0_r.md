---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Sit `n : nat`{.var}. Ostendamus `n + 0 = n`{.claim}.

- Ostendamus `n + 0 = n`{.fact} per inductionem in `n`{.fact} (nat, nat_ind):
- Casus 1 (basis): ostendamus `0 = 0`{.claim}.
  - Ex definitione eq (eq_refl), habemus `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Casus 2 (gradus): ostendamus `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Eligamus quaelibet `m : nat`{.var}; ponamus per hypothesim inductionis `m + 0 = m`{.hyp} (IH).
    - Ex definitione eq (eq_refl), habemus `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Per IH habemus `m + 0 = m`{.claim}.
    - Rescribentes per `m + 0 = m`{.fact} a dextra ad sinistram (eq_ind_r), obtinemus `S (m + 0) = S m`{.claim}.
- His casibus exhaustis, unde sequitur `n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
