<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# Nat.le_refl

✅ Let `n : nat`. We prove `n <= n`.

- ✅ Thus we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m` (H).
  - ▫️ Let us choose arbitrarily `n0 : nat`, `m : nat`.
    - ✅ Using lt_eq_cases we get `forall n1 m0 : nat, n1 <= m0 <-> n1 < m0 \/ n1 = m0` .*by exact @Stdlib.Arith.PeanoNat.Nat.lt_eq_cases*
    - ✅ In particular `n0 <= m <-> n0 < m \/ n0 = m`.
    - ✅ Going back to the definition of and (match) in `n0 <= m <-> n0 < m \/ n0 = m`, we prove `n0 < m \/ n0 = m -> n0 <= m`:
      - ▫️ Assume `n0 <= m -> n0 < m \/ n0 = m` (h) and `n0 < m \/ n0 = m -> n0 <= m` (h0).
        - ✅ By h0 we have `n0 < m \/ n0 = m -> n0 <= m`.
- ✅ By definition of or (or_intror), we have `n < n \/ n = n` .*by eapply @or_intror; eauto*
  - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)` .*by exact @Stdlib.Arith.PeanoNat.Nat.eq_equiv*
  - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R` .*by exact @Corelib.Classes.RelationClasses.Equivalence_Reflexive*
  - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x` .*by exact @Corelib.Classes.RelationClasses.reflexivity*
  - ✅ We deduce `forall x : nat, x = x` .*by tauto*
  - ✅ In particular `n = n`, that is `n = n`.
- ✅ By H we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`.
- ✅ We deduce `n <= n`.

