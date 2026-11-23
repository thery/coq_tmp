(* cyp tutorial, example 13: Cyp Lemma (cyp/TUTORIAL-2.md, section 8).

   The proof of chapter 1, written as a Rocq command.  The statement is
   an ordinary lemma statement.  The body is the list of the steps: words
   are strings, formulas are Rocq terms, and the string after a formula
   starts with its class, "{.claim}" or "{.fact}".  A list among the
   parts of a step is the list of its sub-steps. *)
From Stdlib Require Import Arith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope pstring_scope.

Cyp Lemma double_gt' (n : nat) (h : 0 < n) : n < 2 * n :=
  [ "From" (0 < n) "{.fact} we get" (n + 0 < n + n) "{.claim}." ;
    "This is" (n < 2 * n) "{.claim}." ].
Proof. CypQed.
Check double_gt'.

(* A false step: cyp leaves it as the goal ?c1, which nothing proves. *)
Cyp Lemma wrong (n : nat) (h : 0 < n) : n < 2 * n :=
  [ "We have" (2 * n < n) "{.claim}." ;
    "Hence" (n < 2 * n) "{.claim}." ].
Proof.
  Show.
  Fail lia.
Abort.
