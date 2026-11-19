---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Sia `b : bool`{.var}. Dimostriamo `b = true \/ b = false`{.claim}.

- Dimostriamo `b = true \/ b = false`{.fact} per casi su `b`{.fact} (bool, match):
- Caso 1: dimostriamo `true = true \/ true = false`{.claim}.
  - Per definizione di eq (eq_refl), abbiamo `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Per definizione di or (or_introl), abbiamo `true = true \/ true = false`{.claim} *by Corelib.Init.Logic.or_introl*.
- Caso 2: dimostriamo `false = true \/ false = false`{.claim}.
  - Per definizione di eq (eq_refl), abbiamo `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Per definizione di or (or_intror), abbiamo `false = true \/ false = false`{.claim} *by Corelib.Init.Logic.or_intror*.
- Essendo questi casi esaustivi, ne deduciamo `b = true \/ b = false`{.claim}.
