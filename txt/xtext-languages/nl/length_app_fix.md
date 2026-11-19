---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: nl
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

We bewijzen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- We bewijzen `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} met recursie naar `l1`{.fact} (fix length_app'):
  - Laat `A : Type`{.var} en `l1 l2 : list A`{.var}.
    - We bewijzen `length (l1 ++ l2) = length l1 + length l2`{.fact} met inductie naar `l1`{.fact} (list, match):
    - Geval 1 (basis): we bewijzen `length (nil ++ l2) = length (nil ++ l2)`{.claim}.
      - Volgens de definitie van eq (eq_refl), er geldt `length (nil ++ l2) = length (nil ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - Geval 2 (inductief): we bewijzen `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - Laat `x : A`{.var} en `l : list A`{.var}.
        - Het element `nat`{.fact} behoort tot `Type`{.fact}.
        - Het element `nat`{.fact} behoort tot `Type`{.fact}.
        - Het element `S`{.fact} behoort tot `nat -> nat`{.fact}.
        - Het element `length (l ++ l2)`{.fact} behoort tot `nat`{.fact}.
        - Het element `length l + length l2`{.fact} behoort tot `nat`{.fact}.
        - In het bijzonder `length (l ++ l2) = length l + length l2`{.claim}.
          - Volgens de inductiehypothese (de recursieve aanroep length_app') er geldt `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
        - Door toepassing van f_equal, er geldt `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
    - Deze gevallen zijn uitputtend, hieruit volgt `length (l1 ++ l2) = length l1 + length l2`{.claim}.
