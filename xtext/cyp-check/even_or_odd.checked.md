---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# even_or_odd

✅ Let `n : nat`{.var}. We prove `exists k : nat, n = 2 * k \/ n = 2 * k + 1`{.claim}.

- ▫️ We prove `exists k : nat, n = 2 * k \/ n = 2 * k + 1`{.fact} by induction on `n`{.fact} (nat, two_step):
- ✅ Case 1 (base): we prove `exists k : nat, 0 = 2 * k \/ 0 = 2 * k + 1`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `2 * 0 = 2 * 0`{.claim} *by Corelib.Init.Logic.eq_refl*, that is `0 = 2 * 0`{.fact}.
  - ✅ By definition of or (or_introl), we have `0 = 2 * 0 \/ 0 = 2 * 0 + 1`{.claim} *by Corelib.Init.Logic.or_introl*.
  - ✅ By definition of ex (ex_intro) with witness `0`{.fact}, we have `exists k : nat, 0 = 2 * k \/ 0 = 2 * k + 1`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Case 2 (base): we prove `exists k : nat, 1 = 2 * k \/ 1 = 2 * k + 1`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `2 * 0 + 1 = 2 * 0 + 1`{.claim} *by Corelib.Init.Logic.eq_refl*, that is `1 = 2 * 0 + 1`{.fact}.
  - ✅ By definition of or (or_intror), we have `1 = 2 * 0 \/ 1 = 2 * 0 + 1`{.claim} *by Corelib.Init.Logic.or_intror*.
  - ✅ By definition of ex (ex_intro) with witness `0`{.fact}, we have `exists k : nat, 1 = 2 * k \/ 1 = 2 * k + 1`{.claim} *by Corelib.Init.Logic.ex_intro*.
- ✅ Case 3 (inductive): we prove `forall n0 : nat, (exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1) -> exists k : nat, S (S n0) = 2 * k \/ S (S n0) = 2 * k + 1`{.claim}.
  - ▫️ Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1`{.hyp} (IH).
    - ✅ Going back to the definition of ex (match) in `exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1`{.fact} (IH), we prove `exists k : nat, S (S n0) = 2 * k \/ S (S n0) = 2 * k + 1`{.claim}:
      - ▫️ Let us choose arbitrarily `k : nat`{.var}; assume `n0 = 2 * k \/ n0 = 2 * k + 1`{.hyp} (H).
        - ▫️ We prove `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.fact} by case analysis on `n0 = 2 * k \/ n0 = 2 * k + 1`{.fact} (H) (or, match):
        - ✅ Case 3.1: we prove `n0 = 2 * k -> exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim}.
          - ▫️ Assume `n0 = 2 * k`{.hyp} (Hk).
            - ✅ We have `S (S n0) = 2 * S k \/ S (S n0) = 2 * S k + 1`{.claim} *by lia*.
            - ✅ By definition of ex (ex_intro) with witness `S k`{.fact}, we have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim} *by Corelib.Init.Logic.ex_intro*.
        - ✅ Case 3.2: we prove `n0 = 2 * k + 1 -> exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim}.
          - ▫️ Assume `n0 = 2 * k + 1`{.hyp} (Hk).
            - ✅ We have `S (S n0) = 2 * S k \/ S (S n0) = 2 * S k + 1`{.claim} *by lia*.
            - ✅ By definition of ex (ex_intro) with witness `S k`{.fact}, we have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim} *by Corelib.Init.Logic.ex_intro*.
        - ✅ We have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim} in all cases.
- ❌ These cases being exhaustive, we deduce `exists k : nat, n = 2 * k \/ n = 2 * k + 1`{.claim} *by XText.elim_type.two_step*.

  <details><summary>not proved: exists k : nat, n = 2 * k \/ n = 2 * k + 1</summary></details>

