---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

✅ Sei `m : nat`{.var}. Wir zeigen `m + 0 = m`{.claim}.

- ✅ Wir zeigen `m + 0 = m` durch Induktion über *m*{.just} (*nat*{.just}, *induction*{.just}):
  - ✅ Fall 1 (Anfang): wir zeigen `0 + 0 = 0 + 0`{.claim}.
    - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `0 + 0 = 0 + 0`{.claim}.
  - ✅ Fall 2 (Schritt): wir zeigen `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - ✅ Seien beliebig `m0 : nat`{.var}; angenommen nach Induktionsvoraussetzung `m0 + 0 = m0`{.hyp} (IH).
      - ▫️ Das Element `nat` gehört zu `Type`.
      - ▫️ Das Element `nat` gehört zu `Type`.
      - ▫️ Das Element `S` gehört zu `nat -> nat`.
      - ▫️ Das Element `m0 + 0` gehört zu `nat`.
      - ✅ Nach *IH*{.just} es gilt `m0 + 0 = m0`{.claim}.

      Durch Anwendung von *f_equal*{.just}, es gilt `S (m0 + 0) = S m0`{.claim}.

  Da diese Fälle vollständig sind, daraus folgt `m + 0 = m`{.claim}.
