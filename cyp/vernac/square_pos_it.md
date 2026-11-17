---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: it
---

# square_pos

Siano `a b : Z`. Se `0 < a < b` allora `a * a < b * b`.

- Basta dimostrare `0 < b * b - a * a`.
- Cioè, si riduce a `0 < (b + a) * (b - a)`.
- Da `0 < a < b` abbiamo `0 < b + a` e `0 < b - a`.
