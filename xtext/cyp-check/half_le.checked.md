---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# half_le

✅ Let `n : nat`{.var}. We prove `n / 2 <= n`{.claim}.

- ✅ By definition of nat (*strong_induction*{.just}) on `n`, we prove `n / 2 <= n`{.claim}:
  - ✅ Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `forall m : nat, m < n0 -> m / 2 <= m`{.hyp} (IH).
    - ▫️ The element `2` belongs to `nat`.
    - ✅ Applying *ZifyClasses.rew_iff_rev*{.just}, we have `n0 <= 2 * n0`{.claim}.
      - ▫️ The element `n0 <= 2 * n0` belongs to `Prop`.
      - ▫️ The element `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))` belongs to `Prop`.
      - ✅ Applying *ZifyClasses.mkrel*{.just}, we have `n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
        - ▫️ The element `nat` belongs to `Type`.
        - ▫️ The element `BinNums.Z` belongs to `Type`.
        - ▫️ The element `le` belongs to `nat -> nat -> Prop`.
        - ▫️ The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
        - ▫️ The element `BinInt.Z.le` belongs to `BinNums.Z -> BinNums.Z -> Prop`.
        - ✅ By *Znat.Nat2Z.inj_le*{.just} we have `forall n00 m : nat, n00 <= m <-> BinInt.Z.le (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)`{.claim}.
        - ▫️ The element `BinInt.Z.of_nat n0` belongs to `BinNums.Z`.
        - ✅ By definition of eq (*eq_refl*{.just}), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim}.
        - ▫️ The element `2 * n0` belongs to `nat`.
        - ▫️ The element `BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)` belongs to `BinNums.Z`.
        - ✅ Applying *ZifyClasses.mkapp2*{.just}, we have `BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)`{.claim}.
          - ▫️ The element `nat` belongs to `Type`.
          - ▫️ The element `nat` belongs to `Type`.
          - ▫️ The element `nat` belongs to `Type`.
          - ▫️ The element `BinNums.Z` belongs to `Type`.
          - ▫️ The element `BinNums.Z` belongs to `Type`.
          - ▫️ The element `BinNums.Z` belongs to `Type`.
          - ▫️ The element `Nat.mul` belongs to `nat -> nat -> nat`.
          - ▫️ The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
          - ▫️ The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
          - ▫️ The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
          - ▫️ The element `BinInt.Z.mul` belongs to `BinNums.Z -> BinNums.Z -> BinNums.Z`.
          - ✅ By *Znat.Nat2Z.inj_mul*{.just} we have `forall n00 m : nat, BinInt.Z.of_nat (n00 * m) = BinInt.Z.mul (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)`{.claim}.
          - ▫️ The element `2` belongs to `nat`.
          - ▫️ The element `BinNums.Zpos (BinNums.xO BinNums.xH)` belongs to `BinNums.Z`.
          - ✅ By definition of eq (*eq_refl*{.just}), we have `BinNums.Zpos (BinNums.xO BinNums.xH) = BinNums.Zpos (BinNums.xO BinNums.xH)`{.claim}.
          - ▫️ The element `BinInt.Z.of_nat n0` belongs to `BinNums.Z`.
          - ✅ By definition of eq (*eq_refl*{.just}), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim}.
      - ✅ Applying *__arith*{.just}, we have `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
        - ✅ Applying *Znat.Nat2Z.is_nonneg*{.just} to n0, we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim} (cstr).
        - ✅ We have proved `forall __x10 : BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 (VarMap.Elt __x10))) (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt))`{.claim} (__arith).
          - ❌ Let us choose arbitrarily `__x1 : BinNums.Z`{.var}. Let `__wit : list ZMicromega.ZArithProof := nil`{.var}. Let `__varmap : VarMap.t BinNums.Z := VarMap.Elt __x1`{.var}. Let `__ff : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp := Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt)`{.var}.

            <details><summary>not proved: Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff</summary></details>

            - ✅ By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
            - ▫️ The element `VarMap.find BinNums.Z0 __varmap` belongs to `RingMicromega.PolEnv BinNums.Z`.

            Applying *ZMicromega.ZTautoChecker_sound*{.just}, we have `Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff`{.claim}.
        - ▫️ The element `BinInt.Z.of_nat n0` belongs to `BinNums.Z`.
        - ✅ By *cstr*{.just} we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim}.

    Applying *PeanoNat.Nat.Div0.div_le_upper_bound*{.just}, we have `n0 / 2 <= n0`{.claim}.
