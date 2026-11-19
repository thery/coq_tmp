---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

✅ Wir zeigen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- ✅ Wir zeigen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} durch Rekursion über `l1` (fix length_app'):
  - ✅ Sei `A : Type`{.var} und `l1 l2 : list A`{.var}. Wir zeigen `length (l1 ++ l2) = length l1 + length l2` durch Induktion über `l1` (list, match):
    - ✅ Fall 1 (Anfang): wir zeigen `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - ✅ Fall 2 (Schritt): wir zeigen `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - ✅ Sei `x : A`{.var} und `l : list A`{.var}.
        - ▫️ Das Element `nat` gehört zu `Type`.
        - ▫️ Das Element `nat` gehört zu `Type`.
        - ▫️ Das Element `S` gehört zu `nat -> nat`.
        - ▫️ Das Element `length (l ++ l2)` gehört zu `nat`.
        - ▫️ Das Element `length l + length l2` gehört zu `nat`.
        - ✅ Insbesondere `length (l ++ l2) = length l + length l2`{.claim}.
          - ✅ Nach Induktionsvoraussetzung (dem rekursiven Aufruf length_app') es gilt `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

        Durch Anwendung von *f_equal*{.just}, es gilt `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.

    Da diese Fälle vollständig sind, daraus folgt `length (l1 ++ l2) = length l1 + length l2`{.claim}.
