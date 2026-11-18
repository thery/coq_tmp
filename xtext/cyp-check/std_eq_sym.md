---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# eq_sym

Let `A : Type`{.var}. Let `x y : A`{.var}. Assume `x = y`{.hyp} (H). We prove `y = x`{.claim}.

- Going back to the definition of eq (match) in `x = y`{.fact} (H), we prove `y = x`{.claim}:
  - By definition of eq (eq_refl), we have `x = x`{.claim} *by Corelib.Init.Logic.eq_refl*.
