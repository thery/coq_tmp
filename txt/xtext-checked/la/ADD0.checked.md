---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Sit `m : nat`{.var}. Ostendamus `m + 0 = m`{.claim}.

- ✅ Ostendamus `m + 0 = m` per inductionem in *m*{.just} (*nat*{.just}, *induction*{.just}):
  - ✅ Casus 1 (basis): ostendamus `0 + 0 = 0 + 0`{.claim}.
    - ✅ Ex definitione eq (*eq_refl*{.just}), habemus `0 + 0 = 0 + 0`{.claim}.
  - ✅ Casus 2 (gradus): ostendamus `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - ✅ Eligamus quaelibet `m0 : nat`{.var}; ponamus per hypothesim inductionis `m0 + 0 = m0`{.hyp} (IH).
      - ▫️ Elementum `nat` pertinet ad `Type`.
      - ▫️ Elementum `nat` pertinet ad `Type`.
      - ▫️ Elementum `S` pertinet ad `nat -> nat`.
      - ▫️ Elementum `m0 + 0` pertinet ad `nat`.
      - ✅ Per *IH*{.just} habemus `m0 + 0 = m0`{.claim}.

      Applicando *f_equal*{.just}, habemus `S (m0 + 0) = S m0`{.claim}.

  His casibus exhaustis, unde sequitur `m + 0 = m`{.claim}.
