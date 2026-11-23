---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# defaults

✅ Let `o : option nat`{.var} and `n : nat`{.var}. Assume `n < 3`{.hyp}. We prove `option_map (fun x => x) o = o /\ n <= 2`{.claim}.

- ✅ We have `n <= 2`{.claim}.
- ✅ Whether `o` is `None` or `Some x`, the map changes nothing, so `option_map (fun x => x) o = o`{.claim}.
