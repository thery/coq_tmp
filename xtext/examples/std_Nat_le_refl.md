---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_refl

Let `n : nat`{.var}. We prove `n <= n`{.claim}.

- Thus we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`{.claim} (H).
  - Let us choose arbitrarily `n0 : nat`{.var}, `m : nat`{.var}.
    - Using lt_eq_cases we get `forall n1 m0 : nat, n1 <= m0 <-> n1 < m0 \/ n1 = m0`{.claim} *by exact @lt_eq_cases*.
    - In particular `n0 <= m <-> n0 < m \/ n0 = m`{.claim}.
    - Going back to the definition of and (match) in `n0 <= m <-> n0 < m \/ n0 = m`{.fact}, we prove `n0 < m \/ n0 = m -> n0 <= m`{.claim}:
      - Assume `n0 <= m -> n0 < m \/ n0 = m`{.hyp} (h) and `n0 < m \/ n0 = m -> n0 <= m`{.hyp} (h0).
        - By h0 we have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- By definition of or (or_intror), we have `n < n \/ n = n`{.claim} *by eapply @or_intror; eauto*.
  - We deduce `RelationClasses.Reflexive eq`{.claim}.
    - Using eq_equiv we get `RelationClasses.Equivalence eq`{.claim} *by exact @eq_equiv*.
    - In particular `RelationClasses.Equivalence eq -> RelationClasses.Reflexive eq`{.claim}.
      - Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim} *by exact @Equivalence_Reflexive*.
  - In particular `RelationClasses.Reflexive eq -> forall x : nat, x = x`{.claim}.
    - Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim} *by exact @reflexivity*.
  - We deduce `forall x : nat, x = x`{.claim}.
  - In particular `n = n`{.claim}.
- In particular `n < n \/ n = n -> n <= n`{.claim}.
  - By H we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- We deduce `n <= n`{.claim}.
