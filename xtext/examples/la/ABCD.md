---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: la
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

Sint `A B C D : Prop`{.var}. Ponamus `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) et `A`{.hyp} (h4). Ostendamus `D`{.claim}.

- Per h4 habemus `A`{.claim}.
- Per h4 habemus `A`{.claim}.
- Per h4 habemus `A`{.claim}.
- Per h3 habemus `A -> C`{.claim}.
- Per h2 habemus `A -> C -> B`{.claim}.
- Per h4 habemus `A`{.claim}.
- Per h3 habemus `A -> C`{.claim}.
- Per h1 habemus `A -> B -> C -> D`{.claim}.
- Unde sequitur `D`{.claim} *by tauto*.
