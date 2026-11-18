---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

We bewijzen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- We bewijzen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} met recursie naar `l1`{.fact} (fix length_app'):
  - Laat `A : Type`{.var}.
  - Laat `l1 l2 : list A`{.var}.
  - We bewijzen `length (l1 ++ l2) = length l1 + length l2`{.fact} met inductie naar `l1`{.fact} (list, match):
  - Geval 1 (basis): we bewijzen `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
    - Volgens de definitie van eq (eq_refl), er geldt `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Geval 2 (inductief): we bewijzen `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Laat `x : A`{.var}.
    - Laat `l : list A`{.var}.
    - Volgens de inductiehypothese (de recursieve aanroep length_app') er geldt `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
    - Met behulp van f_equal we krijgen `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
    - Hieruit volgt `S (length (l ++ l2)) = S (length l + length l2)`{.claim} *by congruence*.
  - Deze gevallen zijn uitputtend, hieruit volgt `length (l1 ++ l2) = length l1 + length l2`{.claim}.
