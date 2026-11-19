---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# half_le

Let `n : nat`{.var}. We prove `n / 2 <= n`{.claim}.

- By definition of nat (strong_induction) on `n`{.fact}, we prove `n / 2 <= n`{.claim}:
  - Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `forall m : nat, m < n0 -> m / 2 <= m`{.hyp} (IH).
    - The element `n0`{.fact} belongs to `nat`{.fact}.
    - The element `2`{.fact} belongs to `nat`{.fact}.
    - The element `n0`{.fact} belongs to `nat`{.fact}.
    - Applying rew_iff_rev, we have `n0 <= 2 * n0`{.claim}.
      - The element `n0 <= 2 * n0`{.fact} belongs to `Prop`{.fact}.
      - The element `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.fact} belongs to `Prop`{.fact}.
      - Applying mkrel, we have `n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
        - The element `nat`{.fact} belongs to `Type`{.fact}.
        - The element `BinNums.Z`{.fact} belongs to `Type`{.fact}.
        - The element `le`{.fact} belongs to `nat -> nat -> Prop`{.fact}.
        - The element `BinInt.Z.of_nat`{.fact} belongs to `nat -> BinNums.Z`{.fact}.
        - The element `BinInt.Z.le`{.fact} belongs to `BinNums.Z -> BinNums.Z -> Prop`{.fact}.
        - By inj_le we have `forall n00 m : nat, n00 <= m <-> BinInt.Z.le (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)`{.claim}.
        - The element `n0`{.fact} belongs to `nat`{.fact}.
        - The element `BinInt.Z.of_nat n0`{.fact} belongs to `BinNums.Z`{.fact}.
        - By definition of eq (eq_refl), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim} *by Corelib.Init.Logic.eq_refl*.
        - The element `2 * n0`{.fact} belongs to `nat`{.fact}.
        - The element `BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)`{.fact} belongs to `BinNums.Z`{.fact}.
        - Applying mkapp2, we have `BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)`{.claim}.
          - The element `nat`{.fact} belongs to `Type`{.fact}.
          - The element `nat`{.fact} belongs to `Type`{.fact}.
          - The element `nat`{.fact} belongs to `Type`{.fact}.
          - The element `BinNums.Z`{.fact} belongs to `Type`{.fact}.
          - The element `BinNums.Z`{.fact} belongs to `Type`{.fact}.
          - The element `BinNums.Z`{.fact} belongs to `Type`{.fact}.
          - The element `Nat.mul`{.fact} belongs to `nat -> nat -> nat`{.fact}.
          - The element `BinInt.Z.of_nat`{.fact} belongs to `nat -> BinNums.Z`{.fact}.
          - The element `BinInt.Z.of_nat`{.fact} belongs to `nat -> BinNums.Z`{.fact}.
          - The element `BinInt.Z.of_nat`{.fact} belongs to `nat -> BinNums.Z`{.fact}.
          - The element `BinInt.Z.mul`{.fact} belongs to `BinNums.Z -> BinNums.Z -> BinNums.Z`{.fact}.
          - By inj_mul we have `forall n00 m : nat, BinInt.Z.of_nat (n00 * m) = BinInt.Z.mul (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)`{.claim}.
          - The element `2`{.fact} belongs to `nat`{.fact}.
          - The element `BinNums.Zpos (BinNums.xO BinNums.xH)`{.fact} belongs to `BinNums.Z`{.fact}.
          - By definition of eq (eq_refl), we have `BinNums.Zpos (BinNums.xO BinNums.xH) = BinNums.Zpos (BinNums.xO BinNums.xH)`{.claim} *by Corelib.Init.Logic.eq_refl*.
          - The element `n0`{.fact} belongs to `nat`{.fact}.
          - The element `BinInt.Z.of_nat n0`{.fact} belongs to `BinNums.Z`{.fact}.
          - By definition of eq (eq_refl), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - Applying __arith, we have `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
        - Applying is_nonneg to n0, we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim} (cstr).
        - We have proved `forall __x10 : BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 (VarMap.Elt __x10))) (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt))`{.claim} (__arith).
          - Let us choose arbitrarily `__x1 : BinNums.Z`{.var}.
            - Let `__wit : list ZMicromega.ZArithProof := nil`{.var}.
            - Let `__varmap : VarMap.t BinNums.Z := VarMap.Elt __x1`{.var}.
            - Let `__ff : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp := Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt)`{.var}.
            - The element `__ff`{.fact} belongs to `Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp`{.fact}.
            - The element `__wit`{.fact} belongs to `list ZMicromega.ZArithProof`{.fact}.
            - By definition of eq (eq_refl), we have `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
            - The element `VarMap.find BinNums.Z0 __varmap`{.fact} belongs to `RingMicromega.PolEnv BinNums.Z`{.fact}.
            - Applying ZTautoChecker_sound, we have `Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff`{.claim}.
        - The element `BinInt.Z.of_nat n0`{.fact} belongs to `BinNums.Z`{.fact}.
        - By cstr we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim}.
    - Applying div_le_upper_bound, we have `n0 / 2 <= n0`{.claim}.
