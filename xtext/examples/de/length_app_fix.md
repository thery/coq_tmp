---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

Wir zeigen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- Wir zeigen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} durch Rekursion über `l1`{.fact} (fix length_app'):
  - Sei `A : Type`{.var}.
  - Seien `l1 l2 : list A`{.var}.
  - Wir zeigen `length (l1 ++ l2) = length l1 + length l2`{.fact} durch Induktion über `l1`{.fact} (list, match):
  - Fall 1 (Anfang): wir zeigen `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - Nach Definition von eq (eq_refl), es gilt `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Fall 2 (Schritt): wir zeigen `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Sei `x : A`{.var}.
    - Sei `l : list A`{.var}.
    - Nach Induktionsvoraussetzung (dem rekursiven Aufruf length_app') es gilt `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
    - Mit f_equal wir erhalten `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - Daraus folgt `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - Da diese Fälle vollständig sind, daraus folgt `length (l1 ++ l2) = length l1 + length l2`{.claim}.
