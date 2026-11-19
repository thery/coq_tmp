---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type.
by: tauto | congruence | lia | firstorder | auto
---

# half_le

Let `n : nat`{.var}. We prove `n / 2 <= n`{.claim}.

- By definition of nat (strong_induction) on `n`{.fact}, we prove `n / 2 <= n`{.claim}:
  - Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `forall m : nat, m < n0 -> m / 2 <= m`{.hyp} (IH).
    - Applying mkapp2 to nat, nat, nat, BinNums.Z, BinNums.Z, BinNums.Z, Nat.mul, BinInt.Z.of_nat, BinInt.Z.of_nat, BinInt.Z.of_nat, BinInt.Z.mul, inj_mul and n0, we have `BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)`{.claim} (P1).
      - The element `2`{.fact} belongs to `nat`{.fact}.
      - The element `BinNums.Zpos (BinNums.xO BinNums.xH)`{.fact} belongs to `BinNums.Z`{.fact}.
      - By definition of eq (eq_refl), we have `BinNums.Zpos (BinNums.xO BinNums.xH) = BinNums.Zpos (BinNums.xO BinNums.xH)`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - The element `BinInt.Z.of_nat n0`{.fact} belongs to `BinNums.Z`{.fact}.
      - By definition of eq (eq_refl), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Applying mkrel to nat, BinNums.Z, le, BinInt.Z.of_nat, BinInt.Z.le, inj_le, n0 and P1, we have `n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim} (P2).
      - The element `BinInt.Z.of_nat n0`{.fact} belongs to `BinNums.Z`{.fact}.
      - By definition of eq (eq_refl), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - The element `2 * n0`{.fact} belongs to `nat`{.fact}.
      - The element `BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)`{.fact} belongs to `BinNums.Z`{.fact}.
    - Applying rew_iff_rev to P2, we have `n0 <= 2 * n0`{.claim} (P3).
      - The element `n0 <= 2 * n0`{.fact} belongs to `Prop`{.fact}.
      - The element `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.fact} belongs to `Prop`{.fact}.
      - Applying __arith to cstr, we have `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
        - Applying is_nonneg to n0, we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim} (cstr).
        - We have proved `forall __x10 : BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 (VarMap.Elt __x10))) (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt))`{.claim} (__arith).
          - Let us choose arbitrarily `__x1 : BinNums.Z`{.var}.
            - Let `__wit : list ZMicromega.ZArithProof := nil`{.var}.
            - Let `__varmap : VarMap.t BinNums.Z := VarMap.Elt __x1`{.var}.
            - Let `__ff : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp := Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt)`{.var}.
            - By definition of eq (eq_refl), we have `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
            - The element `VarMap.find BinNums.Z0 __varmap`{.fact} belongs to `RingMicromega.PolEnv BinNums.Z`{.fact}.
            - Applying ZTautoChecker_sound to __ff and __wit, we have `Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff`{.claim}.
        - The element `BinInt.Z.of_nat n0`{.fact} belongs to `BinNums.Z`{.fact}.
    - The element `2`{.fact} belongs to `nat`{.fact}.
    - Applying div_le_upper_bound to n0, n0 and P3, we have `n0 / 2 <= n0`{.claim}.
