---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
lang: de
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

✅ Sei `b : bool`{.var}. Wir zeigen `b = true \/ b = false`{.claim}.

- ✅ Wir zeigen `b = true \/ b = false` durch Fallunterscheidung über `b` (bool, match):
  - ✅ Fall 1: wir zeigen `true = true \/ true = false`{.claim}.
    - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `true = true`{.claim}.
    - ✅ Nach Definition von or (*or_introl*{.just}), es gilt `true = true \/ true = false`{.claim}.
  - ✅ Fall 2: wir zeigen `false = true \/ false = false`{.claim}.
    - ✅ Nach Definition von eq (*eq_refl*{.just}), es gilt `false = false`{.claim}.
    - ✅ Nach Definition von or (*or_intror*{.just}), es gilt `false = true \/ false = false`{.claim}.

  Da diese Fälle vollständig sind, daraus folgt `b = true \/ b = false`{.claim}.
