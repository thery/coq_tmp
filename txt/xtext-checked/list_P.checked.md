---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.implicit_motive.
by: tauto | congruence | lia | firstorder | auto
---

# list_P

✅ Let `E : Set`{.var}. Let `P : list E -> Prop`{.var}. Assume `P nil`{.hyp} (h0) and `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.hyp} (h1). Let `l0 : list E`{.var}. We prove `P l0`{.claim}.

- ✅ We prove `P l0` by induction on `l0` (list, *list_ind*{.just}):
  - ✅ Case 1 (base): we prove `P nil`{.claim}.
    - ✅ By *h0*{.just} we have `P nil`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.claim}.
    - ✅ By *h1*{.just} we have `forall (x : E) (l : list E), P l -> P (x :: l)%list`{.claim}.

  These cases being exhaustive, we deduce `P l0`{.claim}.
