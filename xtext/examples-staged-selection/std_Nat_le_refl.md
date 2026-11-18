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
- By definition of or (or_intror), we have `n < n \/ n = n`{.claim} *by Corelib.Init.Logic.or_intror*.
  - The element `eq`{.fact} belongs to `Relation_Definitions.relation nat`{.fact}.
  - Applying Equivalence_Reflexive to nat and eq_equiv, we have `RelationClasses.Reflexive (@eq nat)`{.claim}.
    - The element `eq`{.fact} belongs to `Relation_Definitions.relation nat`{.fact}.
  - Applying reflexivity to nat and n, we have `n = n`{.claim}, that is `n = n`{.fact}.
- Applying H to n and n, we have `n <= n`{.claim}.
