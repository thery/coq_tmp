---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# in_cons

Let `A : Type`{.var}. We prove `forall (a b : A) (l : list A), In b l -> In b (a :: l)`{.claim}.

- Let `a b : A`{.var}.
- Let `l : list A`{.var}.
- Assume `In b l`{.hyp} (H).
  - By definition of or (or_intror), from `In b l`{.fact} (H) we deduce `a = b \/ In b l`{.claim} *by eapply @or_intror; eauto*.
