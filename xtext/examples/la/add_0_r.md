---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

Sit `n : nat`{.var}. Ostendamus `n + 0 = n`{.claim}.

- Ut ostendamus `n + 0 = n`{.fact} per inductionem (nat, nat_ind), generalizamus ad `forall n0 : nat, n0 + 0 = n0`{.fact}:
- Casus 1 (basis): ostendamus `0 = 0`{.claim}.
  - Ex definitione eq (eq_refl), habemus `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Casus 2 (gradus): ostendamus `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Consideremus quodlibet `m : nat`{.var}.
    - Ponamus per hypothesim inductionis `m + 0 = m`{.hyp} (IH).
      - Ex definitione eq (eq_refl), habemus `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - Per IH habemus `m + 0 = m`{.claim}.
      - Rescribentes per `m + 0 = m`{.fact} a dextra ad sinistram (eq_ind_r), obtinemus `S (m + 0) = S m`{.claim}.
- His casibus exhaustis, unde sequitur `forall n0 : nat, n0 + 0 = n0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- Speciatim `n + 0 = n`{.claim}.
