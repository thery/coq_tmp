---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.lt_irrefl

Let `x : nat`{.var}. We prove `~ x < x`{.claim}.

- Using compare_lt_iff we get `forall n m : nat, (n ?= m) = Lt <-> n < m`{.claim} *by Stdlib.Arith.PeanoNat.Nat.compare_lt_iff*.
- Rewriting with `(x ?= x) = Eq`{.fact} from right to left (eq_ind_r), we get `(x ?= x) <> Lt`{.claim}.
  - We have proved `Eq = Lt -> False`{.claim}.
    - Assume `Eq = Lt`{.hyp} (H).
      - Going back to the definition of eq (match) in `Eq = Lt`{.fact} (H), we prove `Lt = Lt -> False`{.claim}: (H0).
        - Assume `Eq = Lt`{.hyp} (H0).
          - Rewriting with `Eq = Lt`{.fact} from left to right (eq_ind), we get `match Lt with | Eq => True | _ => False end`{.claim} (H1).
            - By definition of True (I), we have `True`{.claim} *by Corelib.Init.Logic.I*, that is `match Eq with | Eq => True | _ => False end`{.fact}.
            - By H0 we have `Eq = Lt`{.claim}.
          - By contradiction (False, False_ind), from `False`{.fact} (H1) we can deduce `False`{.claim}.
      - By definition of eq (eq_refl), we have `Lt = Lt`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - By H0 we have `Lt = Lt -> False`{.claim}.
      - We deduce `False`{.claim}.
  - In particular `(x ?= x) = Eq`{.claim}.
    - Using compare_refl we get `forall x0 : nat, (x0 ?= x0) = Eq`{.claim} *by Stdlib.Arith.PeanoNat.Nat.compare_refl*.
- We have proved `(x ?= x) = Lt <-> x < x -> Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim}.
  - Assume `(x ?= x) = Lt <-> x < x`{.hyp} (lemma).
    - By lemma we have `(x ?= x) = Lt <-> x < x`{.claim}.
    - Using iff_Symmetric we get `RelationClasses.Symmetric iff`{.claim} *by Corelib.Classes.RelationClasses.iff_Symmetric*.
    - Using symmetry we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Symmetric R -> forall x0 y : A, R x0 y -> R y x0`{.claim} *by Corelib.Classes.RelationClasses.symmetry*.
    - We deduce `Morphisms.Proper (Morphisms.respectful iff (Basics.flip Basics.impl)) not`{.claim}, that is `forall x0 y : Prop, x0 <-> y -> Basics.flip Basics.impl (~ x0) (~ y)`{.fact}.
      - We deduce `RelationClasses.subrelation (Morphisms.respectful iff iff) (Morphisms.respectful iff (Basics.flip Basics.impl))`{.claim}.
        - Using iff_flip_impl_subrelation we get `RelationClasses.subrelation iff (Basics.flip Basics.impl)`{.claim} *by Corelib.Classes.Morphisms.iff_flip_impl_subrelation*.
        - We deduce `forall RB RB' : Relation_Definitions.relation Prop, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful iff RB) (Morphisms.respectful iff RB')`{.claim}.
          - In particular `RelationClasses.subrelation iff iff`{.claim}.
            - Using subrelation_refl we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.subrelation R R`{.claim} *by Corelib.Classes.Morphisms.subrelation_refl*.
          - Using subrelation_respectful we get `forall (A B : Type) (RA' RA : Relation_Definitions.relation A), RelationClasses.subrelation RA' RA -> forall RB RB' : Relation_Definitions.relation B, RelationClasses.subrelation RB RB' -> RelationClasses.subrelation (Morphisms.respectful RA RB) (Morphisms.respectful RA' RB')`{.claim} *by Corelib.Classes.Morphisms.subrelation_respectful*.
      - We deduce `forall R : Relation_Definitions.relation (Prop -> Prop), Init.Unconvertible (Relation_Definitions.relation (Prop -> Prop)) R (Morphisms.respectful iff iff) -> RelationClasses.subrelation (Morphisms.respectful iff iff) R -> Morphisms.Proper R not`{.claim}.
        - Using not_iff_morphism we get `Morphisms.Proper (Morphisms.respectful iff iff) not`{.claim} *by Corelib.Classes.Morphisms_Prop.not_iff_morphism*.
        - Using subrelation_proper we get `forall (A : Type) (R' : Relation_Definitions.relation A) (m : A), Morphisms.Proper R' m -> forall R : Relation_Definitions.relation A, Init.Unconvertible (Relation_Definitions.relation A) R R' -> RelationClasses.subrelation R' R -> Morphisms.Proper R m`{.claim} *by Corelib.Classes.Morphisms.subrelation_proper*.
    - We deduce `Basics.flip Basics.impl (~ x < x) ((x ?= x) <> Lt)`{.claim} *by firstorder*.
- We deduce `~ x < x`{.claim} *by lia*.
