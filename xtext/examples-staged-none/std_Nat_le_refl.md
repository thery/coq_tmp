---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_refl

Let `n : nat`{.var}. We prove `n <= n`{.claim}.

- We have proved `forall n1 m : nat, n1 < m \/ n1 = m -> n1 <= m`{.claim} (H).
  - Let us choose arbitrarily `n0 : nat`{.var}.
    - Let us choose arbitrarily `m : nat`{.var}.
      - By application, we have `forall elpi_ctx_entry_3_ : nat, n0 <= elpi_ctx_entry_3_ <-> n0 < elpi_ctx_entry_3_ \/ n0 = elpi_ctx_entry_3_`{.claim}.
        - By lt_eq_cases we have `forall elpi_ctx_entry_3_ elpi_ctx_entry_4_ : nat, elpi_ctx_entry_3_ <= elpi_ctx_entry_4_ <-> elpi_ctx_entry_3_ < elpi_ctx_entry_4_ \/ elpi_ctx_entry_3_ = elpi_ctx_entry_4_`{.claim}.
        - The element `n0`{.fact} belongs to `nat`{.fact}.
      - The element `m`{.fact} belongs to `nat`{.fact}.
      - By application, we have `n0 <= m <-> n0 < m \/ n0 = m`{.claim}.
      - Going back to the definition of and (match) in `n0 <= m <-> n0 < m \/ n0 = m`{.fact}, we prove `n0 < m \/ n0 = m -> n0 <= m`{.claim}:
        - Assume `n0 <= m -> n0 < m \/ n0 = m`{.hyp} (h).
          - Assume `n0 < m \/ n0 = m -> n0 <= m`{.hyp} (h0).
            - By h0 we have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.
    - We have proved `forall m0 : nat, n0 < m0 \/ n0 = m0 -> n0 <= m0`{.claim}.
- By application, we have `n < n \/ n = n -> n <= n`{.claim}.
  - By application, we have `forall m : nat, n < m \/ n = m -> n <= m`{.claim}.
    - By H we have `forall elpi_ctx_entry_2_ m : nat, elpi_ctx_entry_2_ < m \/ elpi_ctx_entry_2_ = m -> elpi_ctx_entry_2_ <= m`{.claim}.
    - The element `n`{.fact} belongs to `nat`{.fact}.
  - The element `n`{.fact} belongs to `nat`{.fact}.
- By definition of or (or_intror), we have `n < n \/ n = n`{.claim} *by Corelib.Init.Logic.or_intror*.
  - By application, we have `forall x : nat, x = x`{.claim}.
    - By application, we have `forall (_ : @RelationClasses.Reflexive nat (@eq nat)) (x : nat), @eq nat x x`{.claim}.
      - By application, we have `forall R : Relation_Definitions.relation nat, RelationClasses.Reflexive R -> forall x : nat, R x x`{.claim}.
        - By reflexivity we have `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
        - The element `nat`{.fact} belongs to `Type`{.fact}.
      - The element `eq`{.fact} belongs to `Relation_Definitions.relation nat`{.fact}.
    - By application, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
      - By application, we have `forall _ : @RelationClasses.Equivalence nat (@eq nat), @RelationClasses.Reflexive nat (@eq nat)`{.claim}.
        - By application, we have `forall R : Relation_Definitions.relation nat, RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
          - By Equivalence_Reflexive we have `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
          - The element `nat`{.fact} belongs to `Type`{.fact}.
        - The element `eq`{.fact} belongs to `Relation_Definitions.relation nat`{.fact}.
      - By eq_equiv we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - The element `n`{.fact} belongs to `nat`{.fact}.
  - By application, we have `n = n`{.claim}, that is `n = n`{.fact}.
- By application, we have `n <= n`{.claim}.
