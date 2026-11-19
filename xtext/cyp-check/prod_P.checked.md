---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.implicit_motive.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# prod_P

✅ Let `E F : Set`{.var}. Let `P : E * F -> Prop`{.var}. Assume `forall (x : E) (y : F), P (x, y)`{.hyp} (h). Let `p0 : (E * F)%type`{.var}. We prove `P p0`{.claim}.

- ✅ By definition of prod (prod_ind) on `p0`{.fact}, we prove `P p0`{.claim}:
  - ✅ By h we have `forall (x : E) (y : F), P (x, y)`{.claim}.
