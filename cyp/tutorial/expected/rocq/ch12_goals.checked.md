---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# goals

✅ Let `a b : Z`{.var}. Assume `0 <= a`{.hyp} and `0 <= b`{.hyp}. We prove `0 <= Z.sqrt a + Z.sqrt b + a`{.claim}.

- 🔶 **[1]** We have `0 <= Z.sqrt a`{.claim}.

  <details><summary>condition 1, to prove in the Proof block: 0 <= Z.sqrt a</summary></details>

- 🔶 **[2]** Prove `0 <= Z.sqrt b`{.goal}.

  <details><summary>open goal of the text, not tried: condition 2, to prove in the Proof block: 0 <= Z.sqrt b</summary></details>

- ✅ Hence `0 <= Z.sqrt a + Z.sqrt b + a`{.claim}.
