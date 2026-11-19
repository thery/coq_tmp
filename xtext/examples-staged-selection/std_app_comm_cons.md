---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_comm_cons

Let `A : Type`{.var}. Let `x y : list A`{.var}. Let `a : A`{.var}. We prove `a :: x ++ y = (a :: x) ++ y`{.claim}.

- By definition of eq (*eq_refl*{.just}), we have `(a :: x) ++ y = (a :: x) ++ y`{.claim}.
