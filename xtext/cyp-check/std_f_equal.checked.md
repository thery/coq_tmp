---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# f_equal

✅ Let `A B : Type`{.var}. Let `f : A -> B`{.var}. Let `x y : A`{.var}. Assume `x = y`{.hyp} (H). We prove `f x = f y`{.claim}.

- ✅ Going back to the definition of eq (match) in `x = y`{.fact} (H), we prove `f x = f y`{.claim}:
  - ✅ By definition of eq (eq_refl), we have `f x = f x`{.claim} *by Corelib.Init.Logic.eq_refl*.
