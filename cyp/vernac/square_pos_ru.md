---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: ru
---

# square_pos

Пусть `a b : Z`{.var}. Если `0 < a < b`{.hyp}, то `a * a < b * b`{.claim}.

- Достаточно доказать, что `0 < b * b - a * a`{.claim}.
  - Что равносильно `0 < (b + a) * (b - a)`{.claim}.
    - Поскольку `0 < a < b`{.fact}, имеем `0 < b + a /\ 0 < b - a`{.claim}.
