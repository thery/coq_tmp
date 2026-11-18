---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
lang: de
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r'

✅ Sei `n : nat`{.var}. Wir zeigen `n + 0 = n`{.claim}.

- ▫️ Um zu zeigen `n + 0 = n`{.fact} durch Induktion (nat, nat_ind), verallgemeinern wir es zu `forall n0 : nat, n0 + 0 = n0`{.fact}:
- ✅ Fall 1 (Anfang): wir zeigen `0 = 0`{.claim}.
  - ✅ Nach Definition von eq (eq_refl), es gilt `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Fall 2 (Schritt): wir zeigen `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - ▫️ Sei beliebig `m : nat`{.var}.
    - ▫️ Angenommen nach Induktionsvoraussetzung `m + 0 = m`{.hyp} (IH).
      - ✅ Nach Definition von eq (eq_refl), es gilt `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
      - ✅ Nach IH es gilt `m + 0 = m`{.claim}.
      - ✅ Durch Umschreiben mit `m + 0 = m`{.fact} von rechts nach links (eq_ind_r), wir erhalten `S (m + 0) = S m`{.claim}.
- ✅ Da diese Fälle vollständig sind, daraus folgt `forall n0 : nat, n0 + 0 = n0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- ✅ Insbesondere `n + 0 = n`{.claim}.
