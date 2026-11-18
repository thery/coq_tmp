---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# in_cons

✅ Let `A : Type`{.var}. We prove `forall (a b : A) (l : list A), In b l -> In b (a :: l)`{.claim}.

- ▫️ Let `a b : A`{.var} and `l : list A`{.var}; assume `In b l`{.hyp} (H).
  - ✅ By definition of or (or_intror), from `In b l`{.fact} (H) we deduce `a = b \/ In b l`{.claim} *by Corelib.Init.Logic.or_intror*.
