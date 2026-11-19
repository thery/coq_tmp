---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
lang: de
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# S_proof

✅ Seien `A B C : Prop`{.var}. Angenommen `A -> B -> C`{.hyp} (h), `A -> B`{.hyp} (h0) und `A`{.hyp} (h1). Wir zeigen `C`{.claim}.

- ✅ Nach h1 es gilt `A`{.claim}.
- ✅ Durch Anwendung von h0 auf h1, es gilt `B`{.claim}.
- ✅ Durch Anwendung von h, es gilt `C`{.claim}.
