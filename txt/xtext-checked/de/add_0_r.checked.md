---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ Sei `n : nat`{.var}. Wir zeigen `n + 0 = n`{.claim}.

- ✅ Wir zeigen `n + 0 = n` durch Induktion über `n` (nat, *nat_ind*{.just}):
  - ✅ Fall 1 (Anfang): wir zeigen `0 = 0`{.claim}.
    - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `0 = 0`{.claim}.
  - ✅ Fall 2 (Schritt): wir zeigen `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
    - ✅ Seien beliebig `m : nat`{.var}; angenommen nach Induktionsvoraussetzung `m + 0 = m`{.hyp} (IH).
      - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `S m = S m`{.claim}.
      - ✅ Nach *IH*{.just} es gilt `m + 0 = m`{.claim}.

      Durch Umschreiben mit `m + 0 = m`{.fact} von rechts nach links (eq_ind_r), wir erhalten `S (m + 0) = S m`{.claim}.

  Da diese Fälle vollständig sind, daraus folgt `n + 0 = n`{.claim}.
