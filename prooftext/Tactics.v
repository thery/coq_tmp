(* prooftext: the bounded searches that the tools run for a tactic a proof
   text may name (tactics.elpi), so that the reader (cyp) and the writer
   (xtext) run the same one.  firstorder has no bound: on some goals it
   runs for minutes and gigabytes; for the name firstorder both tools run
   bounded_firstorder, a proof search of bounded depth, with no time limit
   (it fails after a bounded number of steps). *)

(* the goal unfolded and introduced, its conjunctions split, and the
   connectives of the hypotheses taken apart; each step removes a binder
   or a connective, so that it ends *)
Ltac decompose_all :=
  repeat (intro || split || match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : _ <-> _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    | H : False |- _ => destruct H
    end).

(* the closing tactic: a proof search of depth 4 with the hypotheses, or
   equational reasoning *)
Ltac gap_close := solve [ eauto 4 | congruence ].

(* first-order reasoning, bounded: what cyp runs for firstorder; the
   second time after a simplification (a function on a constructor) *)
Ltac bounded_firstorder :=
  solve [ decompose_all; gap_close
        | decompose_all; simpl in *; decompose_all; gap_close ].
