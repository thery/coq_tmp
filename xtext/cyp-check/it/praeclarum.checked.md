---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: it
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ Siano `x y z t : Prop`{.var}. Supponiamo `(x -> z) /\ (y -> t)`{.hyp} (h1) e `x /\ y`{.hyp} (h2). Dimostriamo `z /\ t`{.claim}.

- ✅ Tornando alla definizione di *and*{.just} (*match*{.just}) in *h1*{.just}, dimostriamo `z /\ t`{.claim}:
  - ✅ Supponiamo `x -> z`{.hyp} (i) e `y -> t`{.hyp} (j). Tornando alla definizione di *and*{.just} (*match*{.just}) in *h2*{.just}, dimostriamo `z /\ t`{.claim}:
    - ✅ Supponiamo `x`{.hyp} (k) e `y`{.hyp} (l).
      - ✅ Applicando *i*{.just} a *k*{.just}, abbiamo `z`{.claim}.
      - ✅ Applicando *j*{.just} a *l*{.just}, abbiamo `t`{.claim}.

      Dunque per definizione di and (*conj*{.just}), abbiamo `z /\ t`{.claim}.
