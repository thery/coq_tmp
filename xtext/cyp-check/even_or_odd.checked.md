<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type. -->

# even_or_odd

✅ Let `n : nat`. We prove `exists k : nat, n = 2 * k \/ n = 2 * k + 1`.

- ▫️ To prove `exists k : nat, n = 2 * k \/ n = 2 * k + 1` by induction (nat, two_step), we generalise it to `forall n0 : nat, exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1`:
- ✅ Case 1 (base): we prove `exists k : nat, 0 = 2 * k \/ 0 = 2 * k + 1`.
  - ✅ By definition of eq (eq_refl), we have `2 * 0 = 2 * 0` , that is `0 = 2 * 0`.*by eapply @eq_refl; eauto*
  - ✅ By definition of or (or_introl), we have `0 = 2 * 0 \/ 0 = 2 * 0 + 1` .*by eapply @or_introl; eauto*
  - ✅ By definition of ex (ex_intro) with witness `0`, we have `exists k : nat, 0 = 2 * k \/ 0 = 2 * k + 1` .*by eapply @ex_intro; eauto*
- ✅ Case 2 (base): we prove `exists k : nat, 1 = 2 * k \/ 1 = 2 * k + 1`.
  - ✅ By definition of eq (eq_refl), we have `2 * 0 + 1 = 2 * 0 + 1` , that is `1 = 2 * 0 + 1`.*by eapply @eq_refl; eauto*
  - ✅ By definition of or (or_intror), we have `1 = 2 * 0 \/ 1 = 2 * 0 + 1` .*by eapply @or_intror; eauto*
  - ✅ By definition of ex (ex_intro) with witness `0`, we have `exists k : nat, 1 = 2 * k \/ 1 = 2 * k + 1` .*by eapply @ex_intro; eauto*
- ✅ Case 3 (inductive): we prove `forall n0 : nat, (exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1) -> exists k : nat, S (S n0) = 2 * k \/ S (S n0) = 2 * k + 1`.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ▫️ Assume by induction hypothesis `exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1` (IH).
      - ✅ Going back to the definition of ex (match) in `exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1` (IH), we prove `exists k : nat, S (S n0) = 2 * k \/ S (S n0) = 2 * k + 1`:
        - ▫️ Let us consider an arbitrary `k : nat`.
          - ▫️ Assume `n0 = 2 * k \/ n0 = 2 * k + 1` (H).
            - ▫️ We prove `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1` by case analysis on `n0 = 2 * k \/ n0 = 2 * k + 1` (H) (or, match):
            - ✅ Case 3.1: we prove `n0 = 2 * k -> exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`.
              - ▫️ Assume `n0 = 2 * k` (Hk).
                - ✅ We have `S (S n0) = 2 * S k \/ S (S n0) = 2 * S k + 1` .*by lia*
                - ✅ By definition of ex (ex_intro) with witness `S k`, we have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1` .*by eapply @ex_intro; eauto*
            - ✅ Case 3.2: we prove `n0 = 2 * k + 1 -> exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1`.
              - ▫️ Assume `n0 = 2 * k + 1` (Hk).
                - ✅ We have `S (S n0) = 2 * S k \/ S (S n0) = 2 * S k + 1` .*by lia*
                - ✅ By definition of ex (ex_intro) with witness `S k`, we have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1` .*by eapply @ex_intro; eauto*
            - ✅ We have `exists k0 : nat, S (S n0) = 2 * k0 \/ S (S n0) = 2 * k0 + 1` in all cases.
- ✅ These cases being exhaustive, we deduce `forall n0 : nat, exists k : nat, n0 = 2 * k \/ n0 = 2 * k + 1` .*by eapply @two_step; cbv beta; eauto*
- ✅ In particular `exists k : nat, n = 2 * k \/ n = 2 * k + 1`.

