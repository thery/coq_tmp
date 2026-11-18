---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Sei `b : bool`{.var}. Wir zeigen `b = true \/ b = false`{.claim}.

- Wir zeigen `b = true \/ b = false`{.fact} durch Fallunterscheidung über `b`{.fact} (bool, match):
- Fall 1: wir zeigen `true = true \/ true = false`{.claim}.
  - Nach Definition von eq (eq_refl), es gilt `true = true`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Nach Definition von or (or_introl), es gilt `true = true \/ true = false`{.claim} *by Corelib.Init.Logic.or_introl*.
- Fall 2: wir zeigen `false = true \/ false = false`{.claim}.
  - Nach Definition von eq (eq_refl), es gilt `false = false`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - Nach Definition von or (or_intror), es gilt `false = true \/ false = false`{.claim} *by Corelib.Init.Logic.or_intror*.
- Da diese Fälle vollständig sind, daraus folgt `b = true \/ b = false`{.claim}.
