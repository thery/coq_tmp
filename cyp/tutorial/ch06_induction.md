---
require: From Stdlib Require Import List Lia. Import ListNotations.
by: easy | lia
---

# length_app

Let `A : Type`{.var} and `l m : list A`{.var}. We prove `length (l ++ m) = length l + length m`{.claim}.

- By *induction*{.just} on *l*{.just}, we prove `length (l ++ m) = length l + length m`{.claim}:
  - For the empty list, `length ([] ++ m) = length [] + length m`{.claim}, by computation (*easy*{.just}).
  - Let `x : A`{.var} and `l' : list A`{.var}; assume `length (l' ++ m) = length l' + length m`{.hyp} (IH). We prove `length ((x :: l') ++ m) = length (x :: l') + length m`{.claim}:
    - It is `S (length (l' ++ m)) = S (length l' + length m)`{.claim}, by *IH*{.just}.
