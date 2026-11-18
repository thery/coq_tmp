---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# imp_trans

Let `A B C : Prop`{.var}. Assume `A -> B`{.hyp} (f) and `B -> C`{.hyp} (g) and `A`{.hyp} (a). We prove `C`{.claim}.

- By a we have `A`{.claim}.
- By f we have `A -> B`{.claim}.
- By g we have `B -> C`{.claim}.
- We deduce `C`{.claim} *by tauto*.
