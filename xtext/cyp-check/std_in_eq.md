---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# in_eq

Let `A : Type`{.var}. We prove `forall (a : A) (l : list A), In a (a :: l)`{.claim}.

- Let `a : A`{.var} and `l : list A`{.var}.
  - By definition of eq (*eq_refl*{.just}), we have `a = a`{.claim}.

  By definition of or (*or_introl*{.just}), we have `a = a \/ In a l`{.claim}.
