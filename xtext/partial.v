(* Explain inside a proof in progress: the open goals are written
   "Prove G" (L. Théry's thesis, 3.3.3).  Explain_partial ends the proof. *)
From Stdlib Require Import Arith.
From XText Require Import Explain.

(* stopped after the case analysis: two goals *)
Lemma or_swap_partial (A B : Prop) : A \/ B -> B \/ A.
Proof. intros H. destruct H as [a|b].
Explain_partial to "examples/or_swap_partial.md".

(* stopped after the induction: base case done, inductive case open *)
Lemma add_0_r_partial (n : nat) : n + 0 = n.
Proof. induction n as [|m IH]. reflexivity.
Explain_partial to "examples/add_0_r_partial.md".

(* praeclarum, the session of section 3.3.3, stopped after split, then
   after the first conjunct *)
Lemma praeclarum_partial1 (x y z t : Prop) : (x -> z) /\ (y -> t) -> x /\ y -> z /\ t.
Proof. intros [Hxz Hyt] [Hx Hy]. split.
Explain_partial to "examples/praeclarum_partial1.md".

Lemma praeclarum_partial2 (x y z t : Prop) : (x -> z) /\ (y -> t) -> x /\ y -> z /\ t.
Proof. intros [Hxz Hyt] [Hx Hy]. split. apply Hxz. exact Hx.
Explain_partial to "examples/praeclarum_partial2.md".
