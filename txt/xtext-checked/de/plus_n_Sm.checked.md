---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

✅ Seien `n m : nat`{.var}. Wir zeigen `S (n + m) = n + S m`{.claim}.

- ▫️ Wir zeigen `S (n + m) = n + S m`{.fact} durch Induktion über `n`{.fact} (nat, nat_ind):
- ✅ Fall 1 (Anfang): wir zeigen `0 + S m = 0 + S m`{.claim}.
  - ✅ Nach Definition von eq (eq_refl), es gilt `0 + S m = 0 + S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Fall 2 (Schritt): wir zeigen `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - ▫️ Seien beliebig `n0 : nat`{.var}; angenommen nach Induktionsvoraussetzung `S (n0 + m) = n0 + S m`{.hyp} (IH).
    - ✅ Nach Definition von eq (eq_refl), es gilt `S (n0 + S m) = S (n0 + S m)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - ✅ Nach IH es gilt `S (n0 + m) = n0 + S m`{.claim}.
    - ✅ Durch Umschreiben mit `S (n0 + m) = n0 + S m`{.fact} von rechts nach links (eq_ind_r), wir erhalten `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- ✅ Da diese Fälle vollständig sind, daraus folgt `S (n + m) = n + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
