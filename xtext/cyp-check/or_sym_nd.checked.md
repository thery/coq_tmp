---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# or_sym_nd

✅ Let `a b : Prop`{.var}. Assume `a \/ b`{.hyp} (H1). We prove `b \/ a`{.claim}.

- ✅ We prove `b \/ a` by case analysis on *H1*{.just} (or, match):
  - ✅ Case 1: we prove `a -> b \/ a`{.claim}.
    - ✅ Assume `a`{.hyp} (H2). By definition of or (*or_intror*{.just}), from *H2*{.just} we deduce `b \/ a`{.claim}.
  - ✅ Case 2: we prove `b -> b \/ a`{.claim}.
    - ✅ Assume `b`{.hyp} (H3). By definition of or (*or_introl*{.just}), from *H3*{.just} we deduce `b \/ a`{.claim}.

  We have `b \/ a`{.claim} in all cases.
