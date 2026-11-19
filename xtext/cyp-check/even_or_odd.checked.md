---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# even_or_odd

✅ Let `n : nat`{.var}. We prove `exists k : nat, n = 2 * k \/ n = 2 * k + 1`{.claim}.

- ✅ We prove `exists k : nat, n = 2 * k \/ n = 2 * k + 1` by induction on `n` (nat, *two_step*{.just}):
  - ✅ Case 1 (base): we prove `exists k : nat, 0 = 2 * k \/ 0 = 2 * k + 1`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `2 * 0 = 2 * 0`, that is `0 = 2 * 0`{.claim}.
    - ✅ By definition of or (*or_introl*{.just}), we have `0 = 2 * 0 \/ 0 = 2 * 0 + 1`{.claim}.
    - ✅ By definition of ex (*ex_intro*{.just}) with witness `0`, we have `exists k : nat, 0 = 2 * k \/ 0 = 2 * k + 1`{.claim}.
  - ✅ Case 2 (base): we prove `exists k : nat, 1 = 2 * k \/ 1 = 2 * k + 1`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `2 * 0 + 1 = 2 * 0 + 1`, that is `1 = 2 * 0 + 1`{.claim}.
    - ✅ By definition of or (*or_intror*{.just}), we have `1 = 2 * 0 \/ 1 = 2 * 0 + 1`{.claim}.
    - ✅ By definition of ex (*ex_intro*{.just}) with witness `0`, we have `exists k : nat, 1 = 2 * k \/ 1 = 2 * k + 1`{.claim}.
  - ✅ Case 3 (inductive): we prove `forall n0 : nat, (exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1) -> exists k : nat, S (S n0) = 2 * k \/ S (S n0) = 2 * k + 1`{.claim}.
    - ✅ Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1`{.hyp} (IH). Going back to the definition of *ex*{.just} (*match*{.just}) in *IH*{.just}, we prove `exists k : nat, S (S n0) = 2 * k \/ S (S n0) = 2 * k + 1`{.claim}:
      - ✅ Let us choose arbitrarily `k : nat`{.var}; assume `n0 = 2 * k \/ n0 = 2 * k + 1`{.hyp} (H). We prove `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1` by case analysis on *H*{.just} (*or*{.just}, *match*{.just}):
        - ✅ Case 3.1: we prove `n0 = 2 * k -> exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim}.
          - ✅ Assume `n0 = 2 * k`{.hyp} (Hk).
            - ✅ By *lia*{.just} we have `S (S n0) = 2 * S k \/ S (S n0) = 2 * S k + 1`{.claim}.

            By definition of ex (*ex_intro*{.just}) with witness `S k`, we have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim}.
        - ✅ Case 3.2: we prove `n0 = 2 * k + 1 -> exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim}.
          - ✅ Assume `n0 = 2 * k + 1`{.hyp} (Hk).
            - ✅ By *lia*{.just} we have `S (S n0) = 2 * S k \/ S (S n0) = 2 * S k + 1`{.claim}.

            By definition of ex (*ex_intro*{.just}) with witness `S k`, we have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim}.

        We have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`{.claim} in all cases.

  These cases being exhaustive, we deduce `exists k : nat, n = 2 * k \/ n = 2 * k + 1`{.claim}.
