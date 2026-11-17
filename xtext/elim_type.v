(* Elimination principles recognised by their type (Coscoy's thesis,
   6.4.2), not by their name: two user-defined induction principles. *)
From Stdlib Require Import Arith Lia.
From XText Require Import Explain.

(* course-of-values induction *)
Lemma strong_induction (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
  intros H n. enough (G : forall k, k <= n -> P k) by (apply G; lia).
  induction n as [|n IH]; intros k Hk.
  - apply H. intros m Hm. lia.
  - apply H. intros m Hm. apply IH. lia.
Qed.

(* induction two by two, with two base cases (as list_2_ind in 6.4.2) *)
Lemma two_step (P : nat -> Prop) :
  P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n.
Proof.
  intros H0 H1 HS n. enough (G : P n /\ P (S n)) by apply G.
  induction n as [|n [IH1 IH2]]; split; auto.
Qed.

(* proofs that use them *)
Lemma half_le (n : nat) : n / 2 <= n.
Proof.
  induction n as [n IH] using strong_induction.
  apply Nat.Div0.div_le_upper_bound. lia.
Qed.
Time Explain half_le to "examples/half_le.md".

Lemma even_or_odd (n : nat) : exists k, n = 2 * k \/ n = 2 * k + 1.
Proof.
  induction n as [| |n IH] using two_step.
  - exists 0. left. reflexivity.
  - exists 0. right. reflexivity.
  - destruct IH as [k [Hk|Hk]]; exists (S k); [left|right]; lia.
Qed.
Time Explain even_or_odd to "examples/even_or_odd.md".
