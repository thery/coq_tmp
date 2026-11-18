---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Nat.le_refl

✅ Let `n : nat`{.var}. We prove `n <= n`{.claim}.

- ✅ Thus we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`{.claim} (H).
  - ▫️ Let us choose arbitrarily `n0 : nat`{.var}, `m : nat`{.var}.
    - ✅ Using lt_eq_cases we get `forall n1 m0 : nat, n1 <= m0 <-> n1 < m0 \/ n1 = m0`{.claim} *by Stdlib.Arith.PeanoNat.Nat.lt_eq_cases*.
    - ✅ In particular `n0 <= m <-> n0 < m \/ n0 = m`{.claim}.
    - ✅ Going back to the definition of and (match) in `n0 <= m <-> n0 < m \/ n0 = m`{.fact}, we prove `n0 < m \/ n0 = m -> n0 <= m`{.claim}:
      - ▫️ Assume `n0 <= m -> n0 < m \/ n0 = m`{.hyp} (h) and `n0 < m \/ n0 = m -> n0 <= m`{.hyp} (h0).
        - ✅ By h0 we have `n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- ✅ By definition of or (or_intror), we have `n < n \/ n = n`{.claim} *by Corelib.Init.Logic.or_intror*.
  - ✅ Using eq_equiv we get `RelationClasses.Equivalence (@eq nat)`{.claim} *by Stdlib.Arith.PeanoNat.Nat.eq_equiv*.
  - ✅ Using Equivalence_Reflexive we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Equivalence R -> RelationClasses.Reflexive R`{.claim} *by Corelib.Classes.RelationClasses.Equivalence_Reflexive*.
  - ✅ Using reflexivity we get `forall (A : Type) (R : Relation_Definitions.relation A), RelationClasses.Reflexive R -> forall x : A, R x x`{.claim} *by Corelib.Classes.RelationClasses.reflexivity*.
  - ✅ We deduce `forall x : nat, x = x`{.claim} *by tauto*.
  - ✅ In particular `n = n`{.claim}, that is `n = n`{.fact}.
- ✅ By H we have `forall n0 m : nat, n0 < m \/ n0 = m -> n0 <= m`{.claim}.
- ✅ We deduce `n <= n`{.claim}.
