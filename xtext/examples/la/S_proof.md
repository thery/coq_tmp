---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

Sint `A B C : Prop`{.var}. Ponamus `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) et `A`{.hyp} (h1). Ostendamus `C`{.claim}.

- Per h1 habemus `A`{.claim}.
- Per h1 habemus `A`{.claim}.
- Per h0 habemus `A -> B`{.claim}.
- Per h habemus `A -> B -> C`{.claim}.
- Unde sequitur `C`{.claim} *by tauto*.
