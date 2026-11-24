---
require: From Stdlib Require Import Reals Lra.
scope: R_scope
by: lra
rules: words_demo.v
---

# words_demo

Let `a b c d : R`{.var}. If `0 <= a <= b`{.hyp} and `0 <= c <= d`{.hyp} then `a * c <= b * d`{.claim}.

- By *monotone product*{.just}, `a * c <= b * c`{.claim}.
- Again `b * c <= b * d`{.claim}, by the *monotone
  product*{.just} (a word cut by the end of a line).
- Also `0 <= b * c`{.claim}, by the *mean value inequality*{.just}, which
  no file declares: an error of the node.
- Hence `a * c <= b * d`{.claim}, by *linear arithmetic*{.just}.
