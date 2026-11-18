---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# imp_trans

✅ Let `A B C : Prop`{.var}. Assume `A -> B`{.hyp} (f), `B -> C`{.hyp} (g) and `A`{.hyp} (a). We prove `C`{.claim}.

- ✅ Applying f to a, we have `B`{.claim}.
- ✅ Applying g, we have `C`{.claim}.
