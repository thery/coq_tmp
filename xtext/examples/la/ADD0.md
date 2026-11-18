---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Sit `m : nat`{.var}. Ostendamus `m + 0 = m`{.claim}.

- Ut ostendamus `m + 0 = m`{.fact} per inductionem (nat, nat_ind), generalizamus ad `forall n : nat, n + 0 = n`{.fact}:
- Casus 1 (basis): ostendamus `0 + 0 = 0 + 0`{.claim}.
  - Ex definitione eq (eq_refl), habemus `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Casus 2 (gradus): ostendamus `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Consideremus quodlibet `m0 : nat`{.var}.
    - Ponamus per hypothesim inductionis `m0 + 0 = m0`{.hyp} (IH).
      - Per IH habemus `m0 + 0 = m0`{.claim}.
      - Adhibentes f_equal obtinemus `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
      - Unde sequitur `S (m0 + 0) = S m0`{.claim}.
- His casibus exhaustis, unde sequitur `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- Speciatim `m + 0 = m`{.claim}.
