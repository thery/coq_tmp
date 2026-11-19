---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_refl

Let `n : nat`{.var}. We prove `n <= n`{.claim}.

- We have proved `forall n1 m0 : nat, n1 < m0 \/ n1 = m0 -> n1 <= m0`{.claim} (H).
  - Let us choose arbitrarily `n0 m : nat`{.var}.
    - Applying *PeanoNat.Nat.lt_eq_cases*{.just} to n0 and m, we have `n0 <= m <-> n0 < m \/ n0 = m`{.claim}.
    - Going back to the definition of *and*{.just} (*match*{.just}) in `n0 <= m <-> n0 < m \/ n0 = m`{.fact}, we prove `n0 < m \/ n0 = m -> n0 <= m`{.claim}:
      - Assume `n0 <= m -> n0 < m \/ n0 = m`{.hyp} (h) and `n0 < m \/ n0 = m -> n0 <= m`{.hyp} (h0). By *h0*{.just} we have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.

    We have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- By definition of or (*or_intror*{.just}), we have `n < n \/ n = n`{.claim}.
  - Applying *RelationClasses.Equivalence_Reflexive*{.just} to nat and *PeanoNat.Nat.eq_equiv*{.just}, we have `RelationClasses.Reflexive (@eq nat)`{.claim} (P1.1).
    - The element `eq` belongs to `Relation_Definitions.relation nat`.
  - The element `eq` belongs to `Relation_Definitions.relation nat`.
  - Applying *RelationClasses.reflexivity*{.just} to nat, P1.1 and n, we have `n = n`, that is `n = n`{.claim}.
- Applying *H*{.just} to n and n, we have `n <= n`{.claim}.
