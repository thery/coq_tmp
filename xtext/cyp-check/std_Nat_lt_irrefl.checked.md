<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.lt_irrefl

✅ Let `x : nat`. We prove `~ x < x`.

- ✅ In particular `(x ?= x) = Lt <-> x < x`.
  - ✅ Using compare_lt_iff we get `forall n m : nat, (n ?= m) = Lt <-> n < m` .*by exact @Stdlib.Arith.PeanoNat.Nat.compare_lt_iff*
- ✅ Rewriting with `(x ?= x) = Eq` from right to left (eq_ind_r), we get `(x ?= x) <> Lt`.
  - ✅ We have proved `Eq = Lt -> False`.
    - ▫️ Assume `Eq = Lt` (H).
      - ✅ Going back to the definition of eq (match) in `Eq = Lt` (H), we prove `Lt = Lt -> False`: (H0).
        - ▫️ Assume `Eq = Lt` (H0).
          - ✅ Rewriting with `Eq = Lt` from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end` (H1).
            - ✅ By definition of True (I), we have `True` .*by eapply @I; eauto*
            - ✅ By H0 we have `Eq = Lt`.
          - ✅ By contradiction (False, False_ind), from `False` (H1) we can deduce `False`.
      - ✅ By definition of eq (eq_refl), we have `Lt = Lt` .*by eapply @eq_refl; eauto*
      - ✅ By H0 we have `Lt = Lt -> False`.
      - ✅ We deduce `False`.
  - ✅ In particular `(x ?= x) = Eq`.
    - ✅ Using compare_refl we get `forall x0 : nat, (x0 ?= x0) = Eq` .*by exact @Stdlib.Arith.PeanoNat.Nat.compare_refl*
- ✅ We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`.
  - ▫️ Assume `(x ?= x) = Lt <-> x < x` (lemma).
    - ✅ We deduce `x < x <-> (x ?= x) = Lt`.
      - ✅ By lemma we have `(x ?= x) = Lt <-> x < x`.
      - ✅ We deduce `forall x0 y : Prop, x0 <-> y -> y <-> x0`.
        - ✅ Using iff_Symmetric we get `RelationClasses.Symmetric iff` .*by exact @Corelib.Classes.RelationClasses.iff_Symmetric*
        - ✅ Using symmetry we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Symmetric R -> forall x0 y : A, R x0 y -> R y x0` .*by exact @Corelib.Classes.RelationClasses.symmetry*
    - ✅ We deduce `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`, that is `forall x0 y : Prop, x0 <-> y -> Basics.flip Basics.impl (~ x0) (~ y)`.
      - ✅ We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`.
        - ✅ Using iff_flip_impl_subrelation we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)` .*by exact @Corelib.Classes.Morphisms.iff_flip_impl_subrelation*
        - ✅ We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`.
          - ✅ In particular `RelationClasses.subrelation iff iff`.
            - ✅ Using subrelation_refl we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R` .*by exact @Corelib.Classes.Morphisms.subrelation_refl*
          - ✅ Using subrelation_respectful we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')` .*by exact @Corelib.Classes.Morphisms.subrelation_respectful*
      - ✅ We deduce `forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`.
        - ✅ Using not_iff_morphism we get `Morphisms.Proper (Morphisms.respectful iff iff) not` .*by exact @Corelib.Classes.Morphisms_Prop.not_iff_morphism*
        - ✅ Using subrelation_proper we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m : A), Morphisms.Proper R' m -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m` .*by exact @Corelib.Classes.Morphisms.subrelation_proper*
    - ✅ We deduce `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`.
- ✅ We deduce `~ x < x`.

