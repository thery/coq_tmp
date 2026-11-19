---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# and_comm

✅ Let `A B : Prop`{.var}. We prove `A /\ B <-> B /\ A`{.claim}.

- ✅ We have proved `A /\ B -> B /\ A`{.claim}.
  - ✅ Assume `A /\ B`{.hyp} (H). Going back to the definition of and (match) in *H*{.just}, we prove `B /\ A`{.claim}:
    - ✅ Assume `A`{.hyp} (H0) and `B`{.hyp} (H00). By definition of and (*conj*{.just}), from *H00*{.just} and *H0*{.just} we deduce `B /\ A`{.claim}.
- ✅ We have proved `B /\ A -> A /\ B`{.claim}.
  - ✅ Assume `B /\ A`{.hyp} (H). Going back to the definition of and (match) in *H*{.just}, we prove `A /\ B`{.claim}:
    - ✅ Assume `B`{.hyp} (H0) and `A`{.hyp} (H00). By definition of and (*conj*{.just}), from *H00*{.just} and *H0*{.just} we deduce `A /\ B`{.claim}.
- ✅ So by definition of and (*conj*{.just}), we have `(A /\ B -> B /\ A) /\ (B /\ A -> A /\ B)`{.claim}.
