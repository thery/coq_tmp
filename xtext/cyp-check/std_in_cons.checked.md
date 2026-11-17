<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# in_cons

✅ Let `A : Type`. We prove `forall (a b : A) (l : list A), In b l -> In b (a :: l)`.

- ▫️ Let `a b : A`.
- ▫️ Let `l : list A`.
- ▫️ Assume `In b l` (H).
  - ✅ By definition of or (or_intror), from `In b l` (H) we deduce `a = b \/ In b l` .*by eapply @or_intror; eauto*

