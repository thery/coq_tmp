---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type.
by: tauto | congruence | lia | firstorder | auto
---

# half_le

Let `n : nat`{.var}. We prove `n / 2 <= n`{.claim}.

- By definition of nat (*strong_induction*{.just}) on `n`, we prove `n / 2 <= n`{.claim}:
  - Let us choose arbitrarily `n0 : nat`{.var}. Assume `forall m : nat, m < n0 -> m / 2 <= m`{.hyp} (IH).
    - By application, we have `n0 <= 2 * n0 -> n0 / 2 <= n0`{.claim}.
      - By application, we have `forall q : nat, n0 <= 2 * q -> n0 / 2 <= q`{.claim}.
        - By application, we have `forall b q : nat, n0 <= b * q -> n0 / b <= q`{.claim}.
          - By *PeanoNat.Nat.Div0.div_le_upper_bound*{.just} we have `forall a b q : nat, a <= b * q -> a / b <= q`{.claim}.
        - The element `2` belongs to `nat`.
    - By application, we have `n0 <= 2 * n0`{.claim}.
      - By application, we have `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)) -> n0 <= 2 * n0`{.claim}.
        - By application, we have `n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)) -> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)) -> n0 <= 2 * n0`{.claim}.
          - By application, we have `forall Q : Prop, n0 <= 2 * n0 <-> Q -> Q -> n0 <= 2 * n0`{.claim}.
            - By *ZifyClasses.rew_iff_rev*{.just} we have `forall P Q : Prop, P <-> Q -> Q -> P`{.claim}.
            - The element `n0 <= 2 * n0` belongs to `Prop`.
          - The element `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))` belongs to `Prop`.
        - By application, we have `n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
          - By application, we have `BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0) -> n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
            - By application, we have `forall t2 : BinNums.Z, BinInt.Z.of_nat (2 * n0) = t2 -> n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) t2`{.claim}.
              - By application, we have `forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> n0 <= s2 <-> BinInt.Z.le (BinInt.Z.of_nat n0) t2`{.claim}.
                - By application, we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> n0 <= s2 <-> BinInt.Z.le (BinInt.Z.of_nat n0) t2`{.claim}.
                  - By application, we have `forall t1 : BinNums.Z, BinInt.Z.of_nat n0 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> n0 <= s2 <-> BinInt.Z.le t1 t2`{.claim}.
                    - By application, we have `forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> s1 <= s2 <-> BinInt.Z.le t1 t2`{.claim}.
                      - By application, we have `(forall n00 m : nat, n00 <= m <-> BinInt.Z.le (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)) -> forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> s1 <= s2 <-> BinInt.Z.le t1 t2`{.claim}.
                        - By application, we have `forall TR : BinNums.Z -> BinNums.Z -> Prop, (forall n00 m : nat, n00 <= m <-> TR (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)) -> forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> s1 <= s2 <-> TR t1 t2`{.claim}.
                          - By application, we have `forall (I : nat -> BinNums.Z) (TR : BinNums.Z -> BinNums.Z -> Prop), (forall n00 m : nat, n00 <= m <-> TR (I n00) (I m)) -> forall (s1 : nat) (t1 : BinNums.Z), I s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), I s2 = t2 -> s1 <= s2 <-> TR t1 t2`{.claim}.
                            - By application, we have `forall (R : nat -> nat -> Prop) (I : nat -> BinNums.Z) (TR : BinNums.Z -> BinNums.Z -> Prop), (forall n00 m : nat, R n00 m <-> TR (I n00) (I m)) -> forall (s1 : nat) (t1 : BinNums.Z), I s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), I s2 = t2 -> R s1 s2 <-> TR t1 t2`{.claim}.
                              - By application, we have `forall (T : Type) (R : nat -> nat -> Prop) (I : nat -> T) (TR : T -> T -> Prop), (forall n00 m : nat, R n00 m <-> TR (I n00) (I m)) -> forall (s1 : nat) (t1 : T), I s1 = t1 -> forall (s2 : nat) (t2 : T), I s2 = t2 -> R s1 s2 <-> TR t1 t2`{.claim}.
                                - By *ZifyClasses.mkrel*{.just} we have `forall (S T : Type) (R : S -> S -> Prop) (I : S -> T) (TR : T -> T -> Prop), (forall n00 m : S, R n00 m <-> TR (I n00) (I m)) -> forall (s1 : S) (t1 : T), I s1 = t1 -> forall (s2 : S) (t2 : T), I s2 = t2 -> R s1 s2 <-> TR t1 t2`{.claim}.
                                - The element `nat` belongs to `Type`.
                              - The element `BinNums.Z` belongs to `Type`.
                            - The element `le` belongs to `nat -> nat -> Prop`.
                          - The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
                        - The element `BinInt.Z.le` belongs to `BinNums.Z -> BinNums.Z -> Prop`.
                      - By *Znat.Nat2Z.inj_le*{.just} we have `forall n00 m : nat, n00 <= m <-> BinInt.Z.le (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)`{.claim}.
                  - The element `BinInt.Z.of_nat n0` belongs to `BinNums.Z`.
                - By definition of eq (*eq_refl*{.just}), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim}.
              - The element `2 * n0` belongs to `nat`.
            - The element `BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)` belongs to `BinNums.Z`.
          - By application, we have `BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)`{.claim}.
            - By application, we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0 -> BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)`{.claim}.
              - By application, we have `forall t2 : BinNums.Z, BinInt.Z.of_nat n0 = t2 -> BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) t2`{.claim}.
                - By application, we have `forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> BinInt.Z.of_nat (2 * s2) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) t2`{.claim}.
                  - By application, we have `BinInt.Z.of_nat 2 = BinNums.Zpos (BinNums.xO BinNums.xH) -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> BinInt.Z.of_nat (2 * s2) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) t2`{.claim}.
                    - By application, we have `forall t1 : BinNums.Z, BinInt.Z.of_nat 2 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> BinInt.Z.of_nat (2 * s2) = BinInt.Z.mul t1 t2`{.claim}.
                      - By application, we have `forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> BinInt.Z.of_nat (s1 * s2) = BinInt.Z.mul t1 t2`{.claim}.
                        - By application, we have `(forall n00 m : nat, BinInt.Z.of_nat (n00 * m) = BinInt.Z.mul (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)) -> forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> BinInt.Z.of_nat (s1 * s2) = BinInt.Z.mul t1 t2`{.claim}.
                          - By application, we have `forall TBOP : BinNums.Z -> BinNums.Z -> BinNums.Z, (forall n00 m : nat, BinInt.Z.of_nat (n00 * m) = TBOP (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)) -> forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> BinInt.Z.of_nat (s1 * s2) = TBOP t1 t2`{.claim}.
                            - By application, we have `forall (I3 : nat -> BinNums.Z) (TBOP : BinNums.Z -> BinNums.Z -> BinNums.Z), (forall n00 m : nat, I3 (n00 * m) = TBOP (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)) -> forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), BinInt.Z.of_nat s2 = t2 -> I3 (s1 * s2) = TBOP t1 t2`{.claim}.
                              - By application, we have `forall (I2 I3 : nat -> BinNums.Z) (TBOP : BinNums.Z -> BinNums.Z -> BinNums.Z), (forall n00 m : nat, I3 (n00 * m) = TBOP (BinInt.Z.of_nat n00) (I2 m)) -> forall (s1 : nat) (t1 : BinNums.Z), BinInt.Z.of_nat s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), I2 s2 = t2 -> I3 (s1 * s2) = TBOP t1 t2`{.claim}.
                                - By application, we have `forall (I1 I2 I3 : nat -> BinNums.Z) (TBOP : BinNums.Z -> BinNums.Z -> BinNums.Z), (forall n00 m : nat, I3 (n00 * m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : nat) (t1 : BinNums.Z), I1 s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), I2 s2 = t2 -> I3 (s1 * s2) = TBOP t1 t2`{.claim}.
                                  - By application, we have `forall (Op : nat -> nat -> nat) (I1 I2 I3 : nat -> BinNums.Z) (TBOP : BinNums.Z -> BinNums.Z -> BinNums.Z), (forall n00 m : nat, I3 (Op n00 m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : nat) (t1 : BinNums.Z), I1 s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
                                    - By application, we have `forall (T3 : Type) (Op : nat -> nat -> nat) (I1 I2 : nat -> BinNums.Z) (I3 : nat -> T3) (TBOP : BinNums.Z -> BinNums.Z -> T3), (forall n00 m : nat, I3 (Op n00 m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : nat) (t1 : BinNums.Z), I1 s1 = t1 -> forall (s2 : nat) (t2 : BinNums.Z), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
                                      - By application, we have `forall (T2 T3 : Type) (Op : nat -> nat -> nat) (I1 : nat -> BinNums.Z) (I2 : nat -> T2) (I3 : nat -> T3) (TBOP : BinNums.Z -> T2 -> T3), (forall n00 m : nat, I3 (Op n00 m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : nat) (t1 : BinNums.Z), I1 s1 = t1 -> forall (s2 : nat) (t2 : T2), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
                                        - By application, we have `forall (T1 T2 T3 : Type) (Op : nat -> nat -> nat) (I1 : nat -> T1) (I2 : nat -> T2) (I3 : nat -> T3) (TBOP : T1 -> T2 -> T3), (forall n00 m : nat, I3 (Op n00 m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : nat) (t1 : T1), I1 s1 = t1 -> forall (s2 : nat) (t2 : T2), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
                                          - By application, we have `forall (S3 T1 T2 T3 : Type) (Op : nat -> nat -> S3) (I1 : nat -> T1) (I2 : nat -> T2) (I3 : S3 -> T3) (TBOP : T1 -> T2 -> T3), (forall n00 m : nat, I3 (Op n00 m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : nat) (t1 : T1), I1 s1 = t1 -> forall (s2 : nat) (t2 : T2), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
                                            - By application, we have `forall (S2 S3 T1 T2 T3 : Type) (Op : nat -> S2 -> S3) (I1 : nat -> T1) (I2 : S2 -> T2) (I3 : S3 -> T3) (TBOP : T1 -> T2 -> T3), (forall (n00 : nat) (m : S2), I3 (Op n00 m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : nat) (t1 : T1), I1 s1 = t1 -> forall (s2 : S2) (t2 : T2), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
                                              - By *ZifyClasses.mkapp2*{.just} we have `forall (S1 S2 S3 T1 T2 T3 : Type) (Op : S1 -> S2 -> S3) (I1 : S1 -> T1) (I2 : S2 -> T2) (I3 : S3 -> T3) (TBOP : T1 -> T2 -> T3), (forall (n00 : S1) (m : S2), I3 (Op n00 m) = TBOP (I1 n00) (I2 m)) -> forall (s1 : S1) (t1 : T1), I1 s1 = t1 -> forall (s2 : S2) (t2 : T2), I2 s2 = t2 -> I3 (Op s1 s2) = TBOP t1 t2`{.claim}.
                                              - The element `nat` belongs to `Type`.
                                            - The element `nat` belongs to `Type`.
                                          - The element `nat` belongs to `Type`.
                                        - The element `BinNums.Z` belongs to `Type`.
                                      - The element `BinNums.Z` belongs to `Type`.
                                    - The element `BinNums.Z` belongs to `Type`.
                                  - The element `Nat.mul` belongs to `nat -> nat -> nat`.
                                - The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
                              - The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
                            - The element `BinInt.Z.of_nat` belongs to `nat -> BinNums.Z`.
                          - The element `BinInt.Z.mul` belongs to `BinNums.Z -> BinNums.Z -> BinNums.Z`.
                        - By *Znat.Nat2Z.inj_mul*{.just} we have `forall n00 m : nat, BinInt.Z.of_nat (n00 * m) = BinInt.Z.mul (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)`{.claim}.
                      - The element `2` belongs to `nat`.
                    - The element `BinNums.Zpos (BinNums.xO BinNums.xH)` belongs to `BinNums.Z`.
                  - By definition of eq (*eq_refl*{.just}), we have `BinNums.Zpos (BinNums.xO BinNums.xH) = BinNums.Zpos (BinNums.xO BinNums.xH)`{.claim}.
              - The element `BinInt.Z.of_nat n0` belongs to `BinNums.Z`.
            - By definition of eq (*eq_refl*{.just}), we have `BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0`{.claim}.
      - By application, we have `BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
        - By application, we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim} (cstr).
          - By *Znat.Nat2Z.is_nonneg*{.just} we have `forall n1 : nat, BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n1)`{.claim}.
        - We have proved `forall __x10 : BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 (VarMap.Elt __x10))) (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt))`{.claim} (__arith).
          - Let us choose arbitrarily `__x1 : BinNums.Z`{.var}. Let `__wit : list ZMicromega.ZArithProof := nil`{.var}. Let `__varmap : VarMap.t BinNums.Z := VarMap.Elt __x1`{.var}. Let `__ff : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp := Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt)`{.var}.
            - By application, we have `forall env : RingMicromega.PolEnv BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula env) __ff`{.claim}.
              - By application, we have `ZMicromega.ZTautoChecker __ff __wit = true -> forall env : RingMicromega.PolEnv BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula env) __ff`{.claim}.
                - By application, we have `forall w : list ZMicromega.ZArithProof, ZMicromega.ZTautoChecker __ff w = true -> forall env : RingMicromega.PolEnv BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula env) __ff`{.claim}.
                  - By *ZMicromega.ZTautoChecker_sound*{.just} we have `forall (f : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp) (w : list ZMicromega.ZArithProof), ZMicromega.ZTautoChecker f w = true -> forall env : RingMicromega.PolEnv BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula env) f`{.claim}.
              - By definition of eq (*eq_refl*{.just}), we have `true = true`{.claim}.
            - The element `VarMap.find BinNums.Z0 __varmap` belongs to `RingMicromega.PolEnv BinNums.Z`.

            By application, we have `Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff`{.claim}.
        - By application, we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0) -> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))`{.claim}.
          - By *__arith*{.just} we have `forall __x1 : BinNums.Z, BinInt.Z.le BinNums.Z0 __x1 -> BinInt.Z.le __x1 (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) __x1)`{.claim}.
          - The element `BinInt.Z.of_nat n0` belongs to `BinNums.Z`.
        - By *cstr*{.just} we have `BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)`{.claim}.

    By application, we have `n0 / 2 <= n0`{.claim}.
