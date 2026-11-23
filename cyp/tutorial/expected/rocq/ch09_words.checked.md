---
require: From Stdlib Require Import Arith Lia.
rules: ch09_words_rules.v
---

# words

✅ Let `a b c d : nat`{.var}. If `a <= b`{.hyp} (hab) and `c <= d`{.hyp} (hcd) then `a * c <= b * d`{.claim}.

- ✅ By *monotonicity*{.just}, `a * c <= b * c`{.claim} (s1).
- ✅ Again by *monotonicity*{.just}, `b * c <= b * d`{.claim} (s2).
- ✅ By *arithmetic*{.just}, `a * c <= b * d`{.claim}.
- ❌ By *monotonicity*{.just}, `a + c <= b + d`{.claim}: no rule fits a sum.

  <details><summary>not proved: a + c <= b + d</summary></details>

