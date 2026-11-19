---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: la
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

✅ Sint `n m : nat`{.var}. Ostendamus `S (n + m) = n + S m`{.claim}.

- ▫️ Ostendamus `S (n + m) = n + S m`{.fact} per inductionem in `n`{.fact} (nat, nat_ind):
- ✅ Casus 1 (basis): ostendamus `0 + S m = 0 + S m`{.claim}.
  - ✅ Ex definitione eq (eq_refl), habemus `0 + S m = 0 + S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Casus 2 (gradus): ostendamus `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - ▫️ Eligamus quaelibet `n0 : nat`{.var}; ponamus per hypothesim inductionis `S (n0 + m) = n0 + S m`{.hyp} (IH).
    - ✅ Ex definitione eq (eq_refl), habemus `S (n0 + S m) = S (n0 + S m)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - ✅ Per IH habemus `S (n0 + m) = n0 + S m`{.claim}.
    - ✅ Rescribentes per `S (n0 + m) = n0 + S m`{.fact} a dextra ad sinistram (eq_ind_r), obtinemus `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- ✅ His casibus exhaustis, unde sequitur `S (n + m) = n + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
