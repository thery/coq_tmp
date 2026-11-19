(* Examples for the rules on inductive types of Coscoy's thesis
   (chapter 6): induction, case analysis, rewriting, fix. *)
From Stdlib Require Import Arith List.
Import ListNotations.
From XText Require Import ExtractText.

(* structural induction on nat, with rewriting *)
Lemma plus_n_Sm' (n m : nat) : S (n + m) = n + S m.
Proof. induction n as [|n IH]. reflexivity. simpl. rewrite IH. reflexivity. Qed.
Time ExtractText plus_n_Sm' to "examples/plus_n_Sm.md".

(* structural induction on lists *)
Lemma app_nil_r' (A : Type) (l : list A) : l ++ [] = l.
Proof. induction l as [|x l IH]. reflexivity. simpl. rewrite IH. reflexivity. Qed.
Time ExtractText app_nil_r' to "examples/app_nil_r.md".

(* rewriting only *)
Lemma eq_trans' (a b c : nat) : a = b -> b = c -> a = c.
Proof. intros H1 H2. rewrite H1. exact H2. Qed.
Time ExtractText eq_trans' to "examples/eq_trans.md".

(* induction on a hypothesis n <= m (a recursive elimination of a
   proposition) *)
Lemma le_n_S' (n m : nat) : n <= m -> S n <= S m.
Proof. intros H. induction H as [|m H IH]. apply le_n. apply le_S. exact IH. Qed.
Time ExtractText le_n_S' to "examples/le_n_S.md".

(* a proof by a fixpoint on nat *)
Fixpoint le_0_n' (n : nat) : 0 <= n :=
  match n with
  | 0 => le_n 0
  | S m => le_S 0 m (le_0_n' m)
  end.
Time ExtractText le_0_n' to "examples/le_0_n_fix.md".

(* a proof by a fixpoint on lists *)
Fixpoint length_app' (A : Type) (l1 l2 : list A) :
  length (l1 ++ l2) = length l1 + length l2 :=
  match l1 with
  | [] => eq_refl
  | x :: l => f_equal S (length_app' A l l2)
  end.
Time ExtractText length_app' to "examples/length_app_fix.md".

(* case analysis on a boolean *)
Lemma bool_cases (b : bool) : b = true \/ b = false.
Proof. destruct b. left. reflexivity. right. reflexivity. Qed.
Time ExtractText bool_cases to "examples/bool_cases.md".
