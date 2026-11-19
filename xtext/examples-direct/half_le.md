---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type.
by: tauto | congruence | lia | firstorder | auto
---

# half_le

Let `n : nat`{.var}. We prove `n / 2 <= n`{.claim}.

- By definition of nat (*strong_induction*{.just}) on `n`, we prove `n / 2 <= n`{.claim}:
  - Let us consider an arbitrary `n0 : nat`{.var}. Assume by induction hypothesis `forall m : nat, m < n0 -> m / 2 <= m`{.hyp} (IH).
    - By *lia*{.just} we deduce `n0 <= 2 * n0`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `BinNums.Zpos (BinNums.xO BinNums.xH) = BinNums.Zpos (BinNums.xO BinNums.xH)`, that is `BinInt.Z.of_nat 2 = BinNums.Zpos (BinNums.xO BinNums.xH)`{.claim}.
      - Using *Znat.Nat2Z.inj_mul*{.just} we get `forall n1 m : nat, BinInt.Z.of_nat (n1 * m) = BinInt.Z.mul (BinInt.Z.of_nat n1) (BinInt.Z.of_nat m)`{.claim}.
      - Using *ZifyClasses.mkapp2*{.just} we get `forall (S1 S2 S3 T1 T2 T3 : Type) (Op : S1 -> S2 -> S3) (I1 : S1 -> T1) (I2 : S2 -> T2) (I3 : S3 -> T3) (TBOP : T1 -> T2 -> T3), (forall (n1 : S1) (m : S2), I3 (Op n1 m) = TBOP (I1 n1) (I2 m)) -> forall (s1 : S1) (t1 : T1), I1 s1 = t1 -> forall (s2 : S2) (t2 : T2), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
      - We deduce `forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> BinInt.Z.of_nat (s1 * s2) = BinInt.Z.mul t1 t2`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim}.
      - Using *Znat.Nat2Z.inj_le*{.just} we get `forall n1 m : nat, n1 <= m <-> BinInt.Z.le (BinInt.Z.of_nat n1) (BinInt.Z.of_nat m)`{.claim}.
      - Using *ZifyClasses.mkrel*{.just} we get `forall (S T : Type) (R : S -> S -> Prop) (I : S -> T) (TR : T -> T -> Prop), (forall n1 m : S, R n1 m <-> TR (I n1) (I m)) -> forall (s1 : S) (t1 : T), I s1 = t1 -> forall (s2 : S) (t2 : T), I s2 = t2 -> R s1 s2 <-> TR t1 t2`{.claim}.
      - We deduce `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
        - In particular `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim} (cstr).
          - Using *Znat.Nat2Z.is_nonneg*{.just} we get `forall n1 : nat, BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n1)`{.claim}.
        - We have `forall __x1 : BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 (VarMap.Elt __x1))) (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt))`{.claim} (__arith), since `__x1` is arbitrary.
          - Let us consider an arbitrary `__x1 : BinNums.Z`{.var}. Let `__wit : list ZMicromega.ZArithProof := nil`{.var}. Let `__varmap : VarMap.t BinNums.Z := VarMap.Elt __x1`{.var}. Let `__ff : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp := Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt)`{.var}.
            - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
            - Using *ZMicromega.ZTautoChecker_sound*{.just} we get `forall (f : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp) (w : list ZMicromega.ZArithProof), ZMicromega.ZTautoChecker f w = true -> forall env : RingMicromega.PolEnv BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula env) f`{.claim}.
            - We deduce `forall env : RingMicromega.PolEnv BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula env) __ff`{.claim}.

            In particular `Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff`{.claim}.
        - By *cstr*{.just} we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim}.
        - By *__arith*{.just} we have `forall __x1 : BinNums.Z, BinInt.Z.le BinNums.Z0 __x1 -> BinInt.Z.le __x1 (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) __x1)`{.claim}.
      - Using *ZifyClasses.rew_iff_rev*{.just} we get `forall P Q : Prop, P <-> Q -> Q -> P`{.claim}.
    - Using *PeanoNat.Nat.Div0.div_le_upper_bound*{.just} we get `forall a b q : nat, a <= b * q -> a / b <= q`{.claim}.

    We deduce `n0 / 2 <= n0`{.claim}.
