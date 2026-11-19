---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: la
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ Sit `n : nat`{.var}. Ostendamus `n + 0 = n`{.claim}.

- ✅ Ostendamus `n + 0 = n` per inductionem in `n` (nat, *nat_ind*{.just}):
  - ✅ Casus 1 (basis): ostendamus `0 = 0`{.claim}.
    - ✅ Ex definitione eq (*eq_refl*{.just}), habemus `0 = 0`{.claim}.
  - ✅ Casus 2 (gradus): ostendamus `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - ✅ Eligamus quaelibet `m : nat`{.var}; ponamus per hypothesim inductionis `m + 0 = m`{.hyp} (IH).
      - ✅ Ex definitione eq (*eq_refl*{.just}), habemus `S m = S m`{.claim}.
      - ✅ Per *IH*{.just} habemus `m + 0 = m`{.claim}.

      Rescribentes per `m + 0 = m`{.fact} a dextra ad sinistram (eq_ind_r), obtinemus `S (m + 0) = S m`{.claim}.

  His casibus exhaustis, unde sequitur `n + 0 = n`{.claim}.
