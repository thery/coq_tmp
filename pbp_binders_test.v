(* Tests of pbp under quantifiers (pbp.v): the four rules of proof by
   pointing for forall and exists, in the goal and in an assumption, alone,
   nested, mixed with the connectives, and in links (two selections).

   The pattern is read positionally: the binders of the pattern stand for
   the binders of the goal at the same place, and give their names to what
   pbp introduces (variables, hypotheses of named premises, destructured
   witnesses) and to the evars it creates (?a: the witness of an exists of
   the goal, the instance of a forall assumption).  An evar left open is a
   goal, after the others; a name of the pattern already used in the
   context is an error.  Each test runs the pbp line, checks the goals it
   leaves (lazymatch goal, and the evar goals by their names [a]: ...), and
   closes the proof. *)

From Stdlib Require Import ssreflect.
From coq_tmp Require Import pbp.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* [fails_with (fun () => ltac1:(tac)) Msg]: tac fails with the message
   Msg (the error of a tactic written in Elpi: "Tactic failure: Msg.") *)
Ltac2 fails_with (tac : unit -> unit) (msg : string) :=
  match Control.case tac with
  | Val _ => Control.throw (Tactic_failure (Some (Message.of_string "fails_with: the tactic did not fail")))
  | Err e =>
    let m := Message.to_string (Message.of_exn e) in
    let nl := String.make 1 (Char.of_int 10) in
    let exp := String.app "Internal" (String.app nl
                 (String.app "err:(Tactic failure: " (String.app msg ".)"))) in
    if String.equal m exp then ()
    else Control.throw (Tactic_failure (Some (Message.concat
           (Message.of_string "fails_with: another message: ") (Message.of_string m))))
  end.

(* ---------- The four rules, alone ---------- *)

(* a forall of the goal: its variable is introduced, named by the pattern *)
Lemma forall_goal : forall n m : nat, n + m = m + n -> True.
Proof.
pbp [X in forall a b : nat, _ -> X].
lazymatch goal with a : nat, b : nat, pbp : a + b = b + a |- True => idtac end.
by [].
Qed.

(* an exists of the goal: its witness is a new evar ?a, a goal after the
   others *)
Lemma exists_goal : exists n : nat, n = 2.
Proof.
pbp [X in exists a, X].
lazymatch goal with |- ?w = 2 => is_evar w end.
[a]: exact 2.
by [].
Qed.

(* a forall assumption: it is used at a new evar ?a; the conclusion is the
   instance, ?a is set to 3 and the proof closes *)
Lemma forall_hyp : (forall n : nat, n + 0 = n) -> 3 + 0 = 3.
Proof.
by pbp [X in (forall a, X) -> _].
Qed.

(* the same, the instance left as a hypothesis (named as the pattern
   variable, as for the other connectives) and ?a as a goal *)
Lemma forall_hyp_open : (forall n : nat, n = 0) -> 1 = 2.
Proof.
pbp [X in (forall a, X) -> _].
lazymatch goal with X : ?w = 0 |- 1 = 2 => is_evar w end.
[a]: exact 1.
by discriminate X.
Qed.

(* an exists assumption: destructured, its variable named by the pattern *)
Lemma exists_hyp : (exists n : nat, n = 0) -> True.
Proof.
pbp [X in (exists k, X) -> _].
lazymatch goal with k : nat, X : k = 0 |- True => idtac end.
by [].
Qed.

(* ---------- Nested quantifiers ---------- *)

(* forall then exists: the evar ?y may use x *)
Lemma forall_exists : forall a : nat, exists b : nat, a = b.
Proof.
pbp [X in forall x, exists y, X].
lazymatch goal with x : nat |- x = ?w => is_evar w end.
[y]: exact x.
by [].
Qed.

(* exists then forall *)
Lemma exists_forall : exists a : nat, forall b : nat, 0 * b = a.
Proof.
pbp [X in exists x, forall y, X].
lazymatch goal with y : nat |- 0 * y = ?w => is_evar w end.
[x]: exact 0.
by [].
Qed.

(* two exists of the goal named alike: the second evar is ?a0, as Rocq
   names it *)
Lemma exists_exists : exists a b : nat, a + 1 = b.
Proof.
pbp [X in exists a, exists a, X].
lazymatch goal with |- ?u + 1 = ?v => is_evar u; is_evar v end.
[a]: exact 1.
[a0]: exact 2.
by [].
Qed.

(* ---------- Mixed with the connectives ---------- *)

(* the conjunct with the exists first, then the other one; the witness ?j
   is set by the first proof *)
Lemma forall_and_exists : forall n : nat, n = n /\ exists m, m = n.
Proof.
pbp [X in forall k, _ /\ exists j, X].
- lazymatch goal with k : nat |- ?w = k => is_evar w end.
  by [].
- lazymatch goal with k : nat |- k = k => idtac end.
  by [].
Qed.

(* a forall assumption whose instance is a conjunction *)
Lemma forall_hyp_and : (forall n : nat, n = n /\ n = 1) -> False.
Proof.
pbp [X in (forall a, _ /\ X) -> _].
lazymatch goal with X : ?w = 1 |- False => is_evar w end.
[a]: exact 0.
by discriminate X.
Qed.

(* an exists assumption inside a disjunction *)
Lemma or_exists_hyp (P : Prop) : P \/ (exists n : nat, n = 1) -> True.
Proof.
pbp [X in _ \/ (exists k, X) -> _].
- lazymatch goal with k : nat, X : k = 1 |- True => idtac end. by [].
- lazymatch goal with pbp : P |- True => idtac end. by [].
Qed.

(* ---------- Names ---------- *)

(* a named premise introduces its hypothesis under that name; an unnamed
   one is pbp *)
Lemma named_premise (A B : Prop) : A /\ B -> B -> A.
Proof.
pbp [X in forall (H : _) (_ : _), X].
lazymatch goal with H : A /\ B, pbp : B |- A => idtac end.
by case: H.
Qed.

(* a name of the pattern already used in the context: the error says which
   name, where it is in the pattern, what uses it *)
Lemma name_clash (A : Prop) (n : nat) (H : True) : A -> forall m : nat, (exists k : nat, k = m) -> A.
Proof.
ltac2:(fails_with (fun () => ltac1:(pbp [X in forall (H : _), _]))
  "pbp: the name H of the premise in the pattern is already used by the hypothesis H : True; choose another name in the pattern").
ltac2:(fails_with (fun () => ltac1:(pbp [X in forall (a : _) (n : nat), _]))
  "pbp: the name n of the forall in the pattern is already used by the variable n : nat; choose another name in the pattern").
ltac2:(fails_with (fun () => ltac1:(pbp [X in forall (a : _) (m : nat), (exists n, X) -> _]))
  "pbp: the name n of the exists in the pattern is already used by the variable n : nat; choose another name in the pattern").
(* a name introduced by the same pbp counts too *)
ltac2:(fails_with (fun () => ltac1:(pbp [X in forall (a : _) (a : nat), _]))
  "pbp: the name a of the forall in the pattern is already used by the hypothesis a : A; choose another name in the pattern").
pbp [X in forall (HA : _) (m : nat), (exists k, X) -> _].
lazymatch goal with HA : A, m : nat, k : nat, X : k = m |- A => idtac end.
by [].
Qed.

(* ---------- Links (two selections) ---------- *)

(* a link sets the instance of a forall assumption: ?a := 2, nothing left
   but the premise of the instance *)
Lemma link_forall_hyp : (forall n : nat, n = n -> n + 0 = n) -> 2 + 0 = 2.
Proof.
pbp [X Y in (forall a, _ -> X) -> Y].
lazymatch goal with |- 2 = 2 => idtac end.
by [].
Qed.

(* an instance set to a variable introduced in the goal *)
Lemma link_forall_forall : (forall n : nat, n = n -> n = 0) -> forall m : nat, m = 0.
Proof.
pbp [X Y in (forall n, _ -> X) -> forall m, Y].
lazymatch goal with m : nat |- m = m => idtac end.
by [].
Qed.

(* an exists assumption used later: its witness is the witness of the goal *)
Lemma link_exists_exists : (exists n : nat, n > 0) -> exists m : nat, m > 0.
Proof.
by pbp [X Y in (exists k, X) -> exists j, Y].
Qed.

(* destructured by a first pbp, used by a second one *)
Lemma exists_hyp_later : (exists n : nat, n = 1) -> exists m : nat, m = 1.
Proof.
pbp [X in (exists k, X) -> _].
lazymatch goal with k : nat, X : k = 1 |- exists m : nat, m = 1 => idtac end.
move: X.
by pbp [X Y in X -> exists j, Y].
Qed.

(* nested: the witness of the goal is the destructured variable, the
   instance of the assumption the introduced one *)
Lemma link_nested : (exists a : nat, forall b : nat, a <= b) ->
  exists c : nat, forall d : nat, c <= d.
Proof.
by pbp [X Y in (exists a, forall b, X) -> exists c, forall d, Y].
Qed.

(* a link between two assumptions, one under a forall *)
(* (?n is set to 1 by the link; the connective rule keeps P 1 as a premise)
   *)
Lemma link_two_hyps (P Q : nat -> Prop) : P 1 -> (forall n, P n -> Q n) -> Q 1.
Proof.
pbp [X Y in X -> (forall n, Y -> _) -> _].
lazymatch goal with pbp : Q 1 |- P 1 -> Q 1 => idtac end.
by [].
Qed.
