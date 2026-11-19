---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Sit `m : nat`{.var}. Ostendamus `m + 0 = m`{.claim}.

- ▫️ Ostendamus `m + 0 = m`{.fact} per inductionem in `m`{.fact} (nat, nat_ind):
- ✅ Casus 1 (basis): ostendamus `0 + 0 = 0 + 0`{.claim}.
  - ✅ Ex definitione eq (eq_refl), habemus `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Casus 2 (gradus): ostendamus `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - ▫️ Eligamus quaelibet `m0 : nat`{.var}; ponamus per hypothesim inductionis `m0 + 0 = m0`{.hyp} (IH).
    - ▫️ Elementum `nat`{.fact} pertinet ad `Type`{.fact}.
    - ▫️ Elementum `nat`{.fact} pertinet ad `Type`{.fact}.
    - ▫️ Elementum `S`{.fact} pertinet ad `nat -> nat`{.fact}.
    - ▫️ Elementum `m0 + 0`{.fact} pertinet ad `nat`{.fact}.
    - ▫️ Elementum `m0`{.fact} pertinet ad `nat`{.fact}.
    - ✅ Per IH habemus `m0 + 0 = m0`{.claim}.
    - ✅ Applicando f_equal, habemus `S (m0 + 0) = S m0`{.claim}.
- ✅ His casibus exhaustis, unde sequitur `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
