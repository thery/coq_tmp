(* prooftext: the bounded searches that the tools run for a tactic a proof
   text may name (tactics.elpi), so that the reader (cyp) and the writer
   (xtext) run the same one.  firstorder has no bound: on some goals it
   runs for minutes and gigabytes; for the name firstorder both tools run
   bounded_firstorder, a proof search of bounded depth, with no time limit
   (it fails after a bounded number of steps). *)

(* the number of steps of decompose_all on one goal: each step is an
   intro, a split or a hypothesis taken apart *)
Ltac decompose_steps := constr:(200%nat).

(* the goal unfolded and introduced, its conjunctions split, and the
   connectives of the hypotheses taken apart, at most n steps deep (n a
   nat).  Without the bound it may not end: split applies the constructor
   of any inductive type with one constructor, and on
     Inductive U : nat -> Prop := cu : forall n, U (S n) -> U n.
   the goal U 0 gives U 1, U 2, ... for ever *)
Ltac decompose_n n :=
  lazymatch n with
  | S ?m =>
      tryif once (intro || split || match goal with
        | H : _ /\ _ |- _ => destruct H
        | H : _ <-> _ |- _ => destruct H
        | H : _ \/ _ |- _ => destruct H
        | H : exists _, _ |- _ => destruct H
        | H : False |- _ => destruct H
        end)
      then decompose_n m else idtac
  | O => idtac
  end.
(* once: the first way only, as repeat does (no backtracking into the steps
   when the tactic after it fails) *)
Ltac decompose_all := let n := decompose_steps in once (decompose_n n).
(* the closing tactic: a proof search of depth 4 with the hypotheses, or
   equational reasoning *)
Ltac gap_close := solve [ eauto 4 | congruence ].

(* first-order reasoning, bounded: what cyp runs for firstorder; the
   second time after a simplification (a function on a constructor) *)
Ltac bounded_firstorder :=
  solve [ decompose_all; gap_close
        | decompose_all; simpl in *; decompose_all; gap_close ].
