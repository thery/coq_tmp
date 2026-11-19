---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: it
---

# square_pos

Siano `a b : Z`{.var}. Se `0 < a < b`{.hyp} allora `a * a < b * b`{.claim}.

- Basta dimostrare `0 < b * b - a * a`{.claim}.
  - Cioè, si riduce a `0 < (b + a) * (b - a)`{.claim}.
    - Da `0 < a < b`{.fact} abbiamo `0 < b + a /\ 0 < b - a`{.claim}.
