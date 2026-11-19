---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.implicit_motive.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# bool_P

✅ Let `P : bool -> Prop`{.var}. Assume `P true`{.hyp} (ht) and `P false`{.hyp} (hf). Let `b0 : bool`{.var}. We prove `P b0`{.claim}.

- ✅ We prove `P b0` by case analysis on *b0*{.just} (*bool*{.just}, *match*{.just}):
  - ✅ Case 1: we prove `P true`{.claim}.
    - ✅ By *ht*{.just} we have `P true`{.claim}.
  - ✅ Case 2: we prove `P false`{.claim}.
    - ✅ By *hf*{.just} we have `P false`{.claim}.

  These cases being exhaustive, we deduce `P b0`{.claim}.
