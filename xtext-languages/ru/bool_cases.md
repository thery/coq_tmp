---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: ru
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Пусть `b : bool`{.var}. Докажем, что `b = true \/ b = false`{.claim}.

- Докажем, что `b = true \/ b = false`{.fact} разбором случаев по `b`{.fact} (bool, match):
- Случай 1: докажем, что `true = true \/ true = false`{.claim}.
  - По определению eq (eq_refl), имеем `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - По определению or (or_introl), имеем `true = true \/ true = false`{.claim} *by Corelib.Init.Logic.or_introl*.
- Случай 2: докажем, что `false = true \/ false = false`{.claim}.
  - По определению eq (eq_refl), имеем `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - По определению or (or_intror), имеем `false = true \/ false = false`{.claim} *by Corelib.Init.Logic.or_intror*.
- Эти случаи исчерпывают все возможности, следовательно `b = true \/ b = false`{.claim}.
