---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# statement_error

Let `a : Z`{.var}. Assume `0 < a +`{.hyp}. We prove `0 < a`{.claim}.

- We have `0 <= a`{.claim}.
