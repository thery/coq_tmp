(* The rules of forall_premise.md: a lemma with a premise on all the
   integers k, which cyp closes by its default tactics (lia) *)
From Stdlib Require Import ZArith Reals Lra Lia.
Local Open Scope R_scope.
(* x = j 2^e - n, with |x| <= c: a bound b of all the integers of the form
   k 2^e - n bounded by c bounds x too *)
Lemma grid_bound (x : R) (j e n c b : Z) :
  x = IZR (j * 2 ^ e - n) -> Rabs x <= IZR c ->
  (forall k : Z, (Z.abs (k * 2 ^ e - n) <= c)%Z -> (Z.abs (k * 2 ^ e - n) <= b)%Z) ->
  Rabs x <= IZR b.
Proof.
  intros -> Hc Hb.
  rewrite <- abs_IZR in *.
  apply IZR_le, Hb, le_IZR, Hc.
Qed.
(* the premises x = IZR (j * 2 ^ e - n) and Rabs x <= IZR c of grid_bound
   have j, e, n, c to be found: a hypothesis gives them *)
Ltac bound_from_hyp := eassumption.
Elpi Accumulate cyp.db lp:{{
  justify {{ (Rabs _ <= IZR _)%R }} (ltac "bound_from_hyp").
  justify {{ _ = IZR _ }} (ltac "bound_from_hyp").
}}.
