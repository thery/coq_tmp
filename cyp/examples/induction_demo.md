---
require: From Stdlib Require Import List Lia. Import ListNotations.
by: easy | auto | lia
---

# length_snoc

Let `A : Type`{.var}, `a : A`{.var} and `l : list A`{.var}. We prove `length (l ++ [a]) = S (length l)`{.claim}.

- By *induction*{.just} on *l*{.just}, of type *list*{.just}, we prove `length (l ++ [a]) = S (length l)`{.claim}:
  - For the empty list, `length ([] ++ [a]) = S (length [])`{.claim}, by computation (*easy*{.just}).
  - Let `x : A`{.var} and `l' : list A`{.var}; assume `length (l' ++ [a]) = S (length l')`{.hyp} (IH). We prove `length ((x :: l') ++ [a]) = S (length (x :: l'))`{.claim}:
    - It is `S (length (l' ++ [a])) = S (S (length l'))`{.claim}, by *IH*{.just}.
