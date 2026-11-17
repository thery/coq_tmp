<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# in_eq

✅ Let `A : Type`. We prove `forall (a : A) (l : list A), In a (a :: l)`.

- ▫️ Let `a : A`.
- ▫️ Let `l : list A`.
- ✅ By definition of eq (eq_refl), we have `a = a` .*by eapply @eq_refl; eauto*
- ✅ By definition of or (or_introl), we have `a = a \/ In a l` .*by eapply @or_introl; eauto*

