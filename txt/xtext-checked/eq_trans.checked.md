---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# eq_trans'

✅ Let `a b c : nat`{.var}. Assume `a = b`{.hyp} (H1) and `b = c`{.hyp} (H2). We prove `a = c`{.claim}.

- ✅ By H2 we have `b = c`{.claim}.
- ✅ By H1 we have `a = b`{.claim}.
- ✅ Rewriting with `a = b`{.fact} from right to left (eq_ind_r), we get `a = c`{.claim}.
