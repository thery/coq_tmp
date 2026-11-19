---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Sei `m : nat`{.var}. Wir zeigen `m + 0 = m`{.claim}.

- ▫️ Wir zeigen `m + 0 = m`{.fact} durch Induktion über `m`{.fact} (nat, nat_ind):
- ✅ Fall 1 (Anfang): wir zeigen `0 + 0 = 0 + 0`{.claim}.
  - ✅ Nach Definition von eq (eq_refl), es gilt `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Fall 2 (Schritt): wir zeigen `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - ▫️ Seien beliebig `m0 : nat`{.var}; angenommen nach Induktionsvoraussetzung `m0 + 0 = m0`{.hyp} (IH).
    - ▫️ Das Element `nat`{.fact} gehört zu `Type`{.fact}.
    - ▫️ Das Element `nat`{.fact} gehört zu `Type`{.fact}.
    - ▫️ Das Element `S`{.fact} gehört zu `nat -> nat`{.fact}.
    - ▫️ Das Element `m0 + 0`{.fact} gehört zu `nat`{.fact}.
    - ▫️ Das Element `m0`{.fact} gehört zu `nat`{.fact}.
    - ✅ Nach IH es gilt `m0 + 0 = m0`{.claim}.
    - ✅ Durch Anwendung von f_equal, es gilt `S (m0 + 0) = S m0`{.claim}.
- ✅ Da diese Fälle vollständig sind, daraus folgt `m + 0 = m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
