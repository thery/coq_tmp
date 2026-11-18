---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: ru
---

# square_pos

Пусть `a b : Z`. Если `0 < a < b`, то `a * a < b * b`.

- Достаточно доказать, что `0 < b * b - a * a`.
- Что равносильно `0 < (b + a) * (b - a)`.
- Поскольку `0 < a < b`, имеем `0 < b + a` и `0 < b - a`.
