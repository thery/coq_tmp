<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper. -->

# or_intro_example

✅ Let `A B C : Prop`. Assume `A` (h). We prove `B \/ A \/ C`.

- ✅ By definition of or (or_introl), from `A` (h) we deduce `A \/ C` .*by eapply @or_introl; eauto*
- ✅ By definition of or (or_intror), we have `B \/ A \/ C` .*by eapply @or_intror; eauto*

