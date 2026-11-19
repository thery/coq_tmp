---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
lang: de
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# ABCD

✅ Seien `A B C D : Prop`{.var}. Angenommen `A -> B -> C -> D`{.hyp} (h1), `A -> C -> B`{.hyp} (h2), `A -> C`{.hyp} (h3) und `A`{.hyp} (h4). Wir zeigen `D`{.claim}.

- ✅ Nach *h4*{.just} es gilt `A`{.claim}.
- ✅ Durch Anwendung von *h2*{.just}, es gilt `B`{.claim}.
  - ✅ Nach *h4*{.just} es gilt `A`{.claim}.
  - ✅ Durch Anwendung von *h3*{.just} auf *h4*{.just}, es gilt `C`{.claim}.
- ✅ Durch Anwendung von *h3*{.just} auf *h4*{.just}, es gilt `C`{.claim}.
- ✅ Durch Anwendung von *h1*{.just}, es gilt `D`{.claim}.
