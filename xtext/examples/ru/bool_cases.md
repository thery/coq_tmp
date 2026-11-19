---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Пусть `b : bool`{.var}. Докажем, что `b = true \/ b = false`{.claim}.

- Докажем, что `b = true \/ b = false` разбором случаев по `b` (bool, match):
  - Случай 1: докажем, что `true = true \/ true = false`{.claim}.
    - По определению eq (*eq_refl*{.just}), имеем `true = true`{.claim}.
    - По определению or (*or_introl*{.just}), имеем `true = true \/ true = false`{.claim}.
  - Случай 2: докажем, что `false = true \/ false = false`{.claim}.
    - По определению eq (*eq_refl*{.just}), имеем `false = false`{.claim}.
    - По определению or (*or_intror*{.just}), имеем `false = true \/ false = false`{.claim}.

  Эти случаи исчерпывают все возможности, следовательно `b = true \/ b = false`{.claim}.
