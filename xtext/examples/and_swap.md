---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# and_swap

Let `A B : Prop`{.var}. Assume `A /\ B`{.hyp} (H). We prove `B /\ A`{.claim}.

- Going back to the definition of and (match) in `A /\ B`{.fact} (H), we prove `B /\ A`{.claim}:
  - Assume `A`{.hyp} (a) and `B`{.hyp} (b).
    - By definition of and (conj), from `B`{.fact} (b) and `A`{.fact} (a) we deduce `B /\ A`{.claim} *by eapply @conj; eauto*.
