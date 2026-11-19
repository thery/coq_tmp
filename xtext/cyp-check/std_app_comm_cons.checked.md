---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# app_comm_cons

✅ Let `A : Type`{.var}. Let `x y : list A`{.var}. Let `a : A`{.var}. We prove `a :: x ++ y = (a :: x) ++ y`{.claim}.

- ✅ By definition of eq (*eq_refl*{.just}), we have `(a :: x) ++ y = (a :: x) ++ y`{.claim}.
