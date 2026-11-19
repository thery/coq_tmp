---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

✅ Wir zeigen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- ✅ Wir zeigen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} durch Rekursion über `l1`{.fact} (fix length_app'):
  - ▫️ Sei `A : Type`{.var} und `l1 l2 : list A`{.var}.
    - ▫️ Wir zeigen `length (l1 ++ l2) = length l1 + length l2`{.fact} durch Induktion über `l1`{.fact} (list, match):
    - ✅ Fall 1 (Anfang): wir zeigen `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - ✅ Nach Definition von eq (eq_refl), es gilt `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - ✅ Fall 2 (Schritt): wir zeigen `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - ▫️ Sei `x : A`{.var} und `l : list A`{.var}.
        - ▫️ Das Element `nat`{.fact} gehört zu `Type`{.fact}.
        - ▫️ Das Element `nat`{.fact} gehört zu `Type`{.fact}.
        - ▫️ Das Element `S`{.fact} gehört zu `nat -> nat`{.fact}.
        - ▫️ Das Element `length (l ++ l2)`{.fact} gehört zu `nat`{.fact}.
        - ▫️ Das Element `length l + length l2`{.fact} gehört zu `nat`{.fact}.
        - ✅ Insbesondere `length (l ++ l2) = length l + length l2`{.claim}.
          - ✅ Nach Induktionsvoraussetzung (dem rekursiven Aufruf length_app') es gilt `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
        - ✅ Durch Anwendung von f_equal, es gilt `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - ✅ Da diese Fälle vollständig sind, daraus folgt `length (l1 ++ l2) = length l1 + length l2`{.claim}.
