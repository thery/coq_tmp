---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_refl

Let `n : nat`{.var}. We prove `n <= n`{.claim}.

- We have proved `forall n1 m : nat, n1 < m \/ n1 = m -> n1 <= m`{.claim} (H).
  - Let us choose arbitrarily `n0 : nat`{.var}.
    - Let us choose arbitrarily `m : nat`{.var}.
      - By application, we have `forall m0 : nat, n0 <= m0 <-> n0 < m0 \/ n0 = m0`{.claim}.
        - By *PeanoNat.Nat.lt_eq_cases*{.just} we have `forall n1 m0 : nat, n1 <= m0 <-> n1 < m0 \/ n1 = m0`{.claim}.
      - By application, we have `n0 <= m <-> n0 < m \/ n0 = m`{.claim}.
      - Going back to the definition of *and*{.just} (*match*{.just}) in `n0 <= m <-> n0 < m \/ n0 = m`{.fact}, we prove `n0 < m \/ n0 = m -> n0 <= m`{.claim}:
        - Assume `n0 <= m -> n0 < m \/ n0 = m`{.hyp} (h). Assume `n0 < m \/ n0 = m -> n0 <= m`{.hyp} (h0). By *h0*{.just} we have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.

      We have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.

    We have proved `forall m0 : nat, n0 < m0 \/ n0 = m0 -> n0 <= m0`{.claim}.
- By application, we have `n < n \/ n = n -> n <= n`{.claim}.
  - By application, we have `forall m : nat, n < m \/ n = m -> n <= m`{.claim}.
    - By *H*{.just} we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- By definition of or (*or_intror*{.just}), we have `n < n \/ n = n`{.claim}.
  - By application, we have `forall x : nat, x = x`{.claim}.
    - By application, we have `forall (_ : @RelationClasses.Reflexive nat (@eq nat)) (x : nat), @eq nat x x`{.claim}.
      - By application, we have `forall R : Relation_Definitions.relation nat, RelationClasses.Reflexive R -> forall x : nat, R x x`{.claim}.
        - By *RelationClasses.reflexivity*{.just} we have `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
        - The element `nat` belongs to `Type`.
      - The element `eq` belongs to `Relation_Definitions.relation nat`.
    - By application, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
      - By application, we have `forall _ : @RelationClasses.Equivalence nat (@eq nat), @RelationClasses.Reflexive nat (@eq nat)`{.claim}.
        - By application, we have `forall R : Relation_Definitions.relation nat, RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
          - By *RelationClasses.Equivalence_Reflexive*{.just} we have `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
          - The element `nat` belongs to `Type`.
        - The element `eq` belongs to `Relation_Definitions.relation nat`.
      - By *PeanoNat.Nat.eq_equiv*{.just} we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - By application, we have `n = n`, that is `n = n`{.claim}.
- By application, we have `n <= n`{.claim}.
