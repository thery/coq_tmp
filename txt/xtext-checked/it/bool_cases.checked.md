---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: it
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

✅ Sia `b : bool`{.var}. Dimostriamo `b = true \/ b = false`{.claim}.

- ✅ Dimostriamo `b = true \/ b = false` per casi su *b*{.just} (*bool*{.just}, *match*{.just}):
  - ✅ Caso 1: dimostriamo `true = true \/ true = false`{.claim}.
    - ✅ Per definizione di eq (*eq_refl*{.just}), abbiamo `true = true`{.claim}.
    - ✅ Per definizione di or (*or_introl*{.just}), abbiamo `true = true \/ true = false`{.claim}.
  - ✅ Caso 2: dimostriamo `false = true \/ false = false`{.claim}.
    - ✅ Per definizione di eq (*eq_refl*{.just}), abbiamo `false = false`{.claim}.
    - ✅ Per definizione di or (*or_intror*{.just}), abbiamo `false = true \/ false = false`{.claim}.

  Essendo questi casi esaustivi, ne deduciamo `b = true \/ b = false`{.claim}.
