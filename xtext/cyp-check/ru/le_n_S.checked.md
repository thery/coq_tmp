---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

✅ Пусть `n m : nat`{.var}. Предположим, что `n <= m`{.hyp} (H). Докажем, что `S n <= S m`{.claim}.

- ✅ Докажем, что `S n <= S m` индукцией по *H*{.just} (le, le_ind):
  - ✅ Случай 1 (база): докажем, что `S n <= S n`{.claim}.
    - ✅ По определению le (*le_n*{.just}), имеем `S n <= S n`{.claim}.
  - ✅ Случай 2 (шаг): докажем, что `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
    - ✅ Выберем произвольно `m0 : nat`{.var}; предположим, что `n <= m0`{.hyp} (H0) и по предположению индукции `S n <= S m0`{.hyp} (IH). По определению le (*le_S*{.just}) со свидетелем `S m0`, из *IH*{.just} следовательно `S n <= S (S m0)`{.claim}.

  Имеем `S n <= S m`{.claim} во всех случаях.
