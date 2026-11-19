(* Small Stdlib-style lemmas, proved with tactics (Qed). *)
From Stdlib Require Import Arith.
From XText Require Import ExtractText.

Lemma and_swap (A B : Prop) : A /\ B -> B /\ A.
Proof. intros [a b]. split. exact b. exact a. Qed.
Time ExtractText and_swap to "examples/and_swap.md".

Lemma or_swap (A B : Prop) : A \/ B -> B \/ A.
Proof. intros [a|b]. right. exact a. left. exact b. Qed.
Time ExtractText or_swap to "examples/or_swap.md".

Lemma imp_trans (A B C : Prop) : (A -> B) -> (B -> C) -> A -> C.
Proof. intros f g a. apply g. apply f. exact a. Qed.
Time ExtractText imp_trans to "examples/imp_trans.md".

Lemma not_not_intro (A : Prop) : A -> ~ ~ A.
Proof. intros a na. apply na. exact a. Qed.
Time ExtractText not_not_intro to "examples/not_not_intro.md".

Lemma ex_forall (P : nat -> nat -> Prop) :
  (exists x, forall y, P x y) -> forall y, exists x, P x y.
Proof. intros [x H] y. exists x. apply H. Qed.
Time ExtractText ex_forall to "examples/ex_forall.md".

Lemma forall_and (P Q : nat -> Prop) :
  (forall x, P x /\ Q x) -> forall x, P x.
Proof. intros H x. destruct (H x) as [p _]. exact p. Qed.
Time ExtractText forall_and to "examples/forall_and.md".

Lemma add_0_r' (n : nat) : n + 0 = n.
Proof. induction n as [|m IH]. reflexivity. simpl. rewrite IH. reflexivity. Qed.
Time ExtractText add_0_r' to "examples/add_0_r.md".

Lemma le_add_r' (n m : nat) : n <= n + m.
Proof. induction m as [|m IH]. rewrite Nat.add_0_r. apply le_n.
  rewrite Nat.add_succ_r. apply le_S. exact IH. Qed.
Time ExtractText le_add_r' to "examples/le_add_r.md".

Lemma double_neg_em (A : Prop) : ~ ~ (A \/ ~ A).
Proof. intros H. apply H. right. intros a. apply H. left. exact a. Qed.
Time ExtractText double_neg_em to "examples/double_neg_em.md".
