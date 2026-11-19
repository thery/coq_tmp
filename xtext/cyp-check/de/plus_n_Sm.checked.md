---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

✅ Seien `n m : nat`{.var}. Wir zeigen `S (n + m) = n + S m`{.claim}.

- ✅ Wir zeigen `S (n + m) = n + S m` durch Induktion über `n` (nat, *nat_ind*{.just}):
  - ✅ Fall 1 (Anfang): wir zeigen `0 + S m = 0 + S m`{.claim}.
    - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `0 + S m = 0 + S m`{.claim}.
  - ✅ Fall 2 (Schritt): wir zeigen `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
    - ✅ Seien beliebig `n0 : nat`{.var}; angenommen nach Induktionsvoraussetzung `S (n0 + m) = n0 + S m`{.hyp} (IH).
      - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `S (n0 + S m) = S (n0 + S m)`{.claim}.
      - ✅ Nach *IH*{.just} es gilt `S (n0 + m) = n0 + S m`{.claim}.

      Durch Umschreiben mit `S (n0 + m) = n0 + S m`{.fact} von rechts nach links (eq_ind_r), wir erhalten `S (S (n0 + m)) = S (n0 + S m)`{.claim}.

  Da diese Fälle vollständig sind, daraus folgt `S (n + m) = n + S m`{.claim}.
