---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_refl

Let `n : nat`{.var}. We prove `n <= n`{.claim}.

- Thus we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`{.claim} (H).
  - Let us choose arbitrarily `n0 : nat`{.var} and `m : nat`{.var}.
    - Using *PeanoNat.Nat.lt_eq_cases*{.just} we get `forall n1 m0 : nat, n1 <= m0 <-> n1 < m0 \/ n1 = m0`{.claim}.
    - In particular `n0 <= m <-> n0 < m \/ n0 = m`{.claim}.
    - Going back to the definition of *and*{.just} (*match*{.just}) in `n0 <= m <-> n0 < m \/ n0 = m`{.fact}, we prove `n0 < m \/ n0 = m -> n0 <= m`{.claim}:
      - Assume `n0 <= m -> n0 < m \/ n0 = m`{.hyp} (h) and `n0 < m \/ n0 = m -> n0 <= m`{.hyp} (h0). By *h0*{.just} we have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.

    We have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- By definition of or (*or_intror*{.just}), we have `n < n \/ n = n`{.claim}.
  - Using *PeanoNat.Nat.eq_equiv*{.just} we get `RelationClasses.Equivalence (@eq nat)`{.claim}.
  - Using *RelationClasses.Equivalence_Reflexive*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim}.
  - Using *RelationClasses.reflexivity*{.just} we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim}.
  - By *tauto*{.just} we deduce `forall x : nat, x = x`{.claim}.
  - In particular `n = n`, that is `n = n`{.claim}.
- By *H*{.just} we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- We deduce `n <= n`{.claim}.
