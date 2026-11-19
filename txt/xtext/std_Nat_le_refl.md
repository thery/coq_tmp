---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_refl

Let `n : nat`{.var}. We prove `n <= n`{.claim}.

- We have proved `forall n1 m0 : nat, n1 < m0 \/ n1 = m0 -> n1 <= m0`{.claim} (H).
  - Let us choose arbitrarily `n0 m : nat`{.var}.
    - Applying lt_eq_cases to n0 and m, we have `n0 <= m <-> n0 < m \/ n0 = m`{.claim}.
    - Going back to the definition of and (match) in `n0 <= m <-> n0 < m \/ n0 = m`{.fact}, we prove `n0 < m \/ n0 = m -> n0 <= m`{.claim}:
      - Assume `n0 <= m -> n0 < m \/ n0 = m`{.hyp} (h) and `n0 < m \/ n0 = m -> n0 <= m`{.hyp} (h0).
        - By h0 we have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- The element `n`{.fact} belongs to `nat`{.fact}.
- The element `n`{.fact} belongs to `nat`{.fact}.
- By definition of or (or_intror), we have `n < n \/ n = n`{.claim} *by Corelib.Init.Logic.or_intror*.
  - The element `nat`{.fact} belongs to `Type`{.fact}.
  - The element `eq`{.fact} belongs to `Relation_Definitions.relation nat`{.fact}.
  - Applying Equivalence_Reflexive, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
    - The element `nat`{.fact} belongs to `Type`{.fact}.
    - The element `eq`{.fact} belongs to `Relation_Definitions.relation nat`{.fact}.
    - By eq_equiv we have `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - The element `n`{.fact} belongs to `nat`{.fact}.
  - Applying reflexivity, we have `n = n`{.claim}, that is `n = n`{.fact}.
- Applying H, we have `n <= n`{.claim}.
