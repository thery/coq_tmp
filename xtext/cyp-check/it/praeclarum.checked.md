---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ Siano `x y z t : Prop`{.var}. Supponiamo `(x -> z) /\ (y -> t)`{.hyp} (h1) e `x /\ y`{.hyp} (h2). Dimostriamo `z /\ t`{.claim}.

- ✅ Tornando alla definizione di and (and_ind) in `(x -> z) /\ (y -> t)`{.fact} (h1), dimostriamo `z /\ t`{.claim}:
  - ▫️ Supponiamo `x -> z`{.hyp} (i) e `y -> t`{.hyp} (j).
    - ✅ Tornando alla definizione di and (and_ind) in `x /\ y`{.fact} (h2), dimostriamo `z /\ t`{.claim}:
      - ▫️ Supponiamo `x`{.hyp} (k) e `y`{.hyp} (l).
        - ✅ Applicando i a k, abbiamo `z`{.claim}.
        - ✅ Applicando j a l, abbiamo `t`{.claim}.
        - ✅ Dunque per definizione di and (conj), abbiamo `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
