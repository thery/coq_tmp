<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas. -->

# double_neg_em

✅ Let `A : Prop`. We prove `~ ~ (A \/ ~ A)`.

- ▫️ Assume `~ (A \/ ~ A)` (H).
  - ✅ By definition of or (or_intror), we have `A \/ ~ A` .*by eapply @or_intror; eauto*
    - ▫️ Assume `A` (a).
      - ✅ By definition of or (or_introl), from `A` (a) we deduce `A \/ ~ A` .*by eapply @or_introl; eauto*
      - ✅ By H we have `~ (A \/ ~ A)`, that is `A \/ ~ A -> False`.
      - ✅ We deduce `False`.
    - ✅ We have proved `A -> False`.
  - ✅ By H we have `~ (A \/ ~ A)`, that is `A \/ ~ A -> False`.
  - ✅ We deduce `False`.

