(* Tests of point_actions.v: the list of the actions, the actions declared
   there (Point, Link, Simplify here, Unfold here), actions declared here
   (dynamically: one by a template, one written in Elpi), the errors.

   [elpi point_run_expect "Name" Line Ws Sel ...] checks that point_run
   gives the line Line for the selections Sel (Ws: the subterms that
   selections were widened to, "" for none); the line is then run.
   [fails_with M t] checks that the tactic t fails with a message that
   contains M (blanks ignored). *)

From Stdlib Require Import ssreflect PeanoNat.
From elpi Require Import elpi.
From coq_tmp Require Import point_actions.
From Ltac2 Require Import Ltac2.

Ltac2 no_blanks (s : string) :=
  let rec go i acc :=
    if Int.lt i 0 then String.concat "" acc else
    let c := String.get s i in
    let n := Char.to_int c in
    if Bool.or (Bool.or (Int.equal n 32) (Int.equal n 10))
          (Bool.or (Int.equal n 9) (Int.equal n 13))
    then go (Int.sub i 1) acc
    else go (Int.sub i 1) (String.make 1 c :: acc) in
  go (Int.sub (String.length s) 1) [].

Ltac2 contains (s : string) (m : string) :=
  let ls := String.length s in
  let lm := String.length m in
  let rec from i :=
    if Int.lt (Int.sub ls lm) i then false
    else if String.equal (String.sub s i lm) m then true
    else from (Int.add i 1) in
  from 0.

Ltac2 fails_with (m : string) (t : unit -> unit) :=
  match Control.case t with
  | Val _ => Control.throw (Tactic_failure (Some (Message.of_string "no failure")))
  | Err e =>
      let s := Message.to_string (Message.of_exn e) in
      if contains (no_blanks s) (no_blanks m) then ()
      else Control.throw (Tactic_failure (Some (Message.concat
             (Message.of_string "unexpected message: ") (Message.of_string s))))
  end.

Set Default Proof Mode "Classic".

Definition double n := n + n.

(* ---------- The list of the actions ---------- *)

Goal True.
Proof.
elpi point_actions.
elpi point_actions_expect "[{""name"":""Point"",""kind"":""point"",""doc"":""pbp: bring the selected subformula to the surface of the goal""},{""name"":""Link"",""kind"":""link"",""doc"":""pbp: link the two selected subformulas""},{""name"":""Simplify here"",""kind"":""point"",""doc"":""simplify the selected subterm (ssreflect's rewrite /=, at the selection)""},{""name"":""Unfold here"",""kind"":""point"",""doc"":""unfold the constant at the head of the selected subterm, in it""}]".
Abort.

(* ---------- Point and Link: the lines of pbp_pattern ---------- *)

Goal forall a b : nat, a + b = b + a.
Proof.
move=> a b.
elpi point_run_expect "Point" "pbp [X in X + _ = _]." "" 0 1.
elpi pbp_pattern_expect "pbp [X in X + _ = _]." "" 0 1.
elpi point_run_expect "Point" "pbp [X in _ = _ + X]." "" 6 7.
elpi point_run_expect "Point" "pbp [X in X + _ = _]." "" 0 0.
Abort.

Goal forall a b c : nat, a + b + c = c.
Proof.
move=> a b c.
elpi point_run_expect "Point" "pbp [X in X = _]." "a + b + c" 2 5.
elpi point_run_expect "Point" "pbp [X in X + _ = _]." "a + b" 1 2.
Abort.

Lemma link_gen (A B : Prop) : A /\ B -> A /\ B.
Proof.
(* A/\B->A/\B *)
elpi point_run_expect "Link" "pbp [X Y in X /\ _ -> Y /\ _]." "" 0 1 6 7.
elpi pbp_pattern_expect "pbp [X Y in X /\ _ -> Y /\ _]." "" 0 1 6 7.
pbp [X Y in X /\ _ -> Y /\ _].
move: pbp.
elpi point_run_expect "Link" "pbp [X Y in X -> _ -> Y]." "" 0 1 6 7.
by pbp [X Y in X -> _ -> Y].
Qed.

(* hypotheses: generalized first *)
Goal forall A B : Prop, (A -> B) -> A -> B.
Proof.
move=> A B ab a.
elpi point_run_expect "Point" "move: ab; pbp [X in (_ -> X) -> _]." "" ab 3 4.
elpi point_run_expect "Link" "move: ab; pbp [X Y in (_ -> X) -> Y]." "" ab 3 4 0 1.
elpi point_run_expect "Link" "move: ab a; pbp [X Y in (Y -> _) -> X -> _]."
  "" a 0 1 ab 0 1.
move: ab; pbp [X Y in (_ -> X) -> Y].
by [].
Qed.

(* the goal selector is the interface's: the action runs on the goal it
   selects *)
Goal forall A B : Prop, A -> B -> A /\ B.
Proof.
move=> A B a b; split.
2: elpi point_run_expect "Point" "pbp [X in X]." "" 0 1.
Abort.

(* ---------- The examples of the README ---------- *)

(* 1+1+a=double(1+a) *)
Goal forall a : nat, 1 + 1 + a = double (1 + a).
Proof.
move=> a.
elpi point_run_expect "Point" "pbp [X in X + _ = _]." "" 0 3.
elpi point_run_expect "Link" "pbp [X Y in X + _ = double Y]." "" 0 3 13 16.
elpi point_run_expect "Simplify here" "rewrite [X in X + _ = _]/=." "" 0 3.
elpi point_run_expect "Unfold here" "rewrite [X in _ = X]/double." "" 6 17.
Abort.

(* ---------- Simplify here ---------- *)

(* 1+1+a=double(1+a) *)
Goal forall a : nat, 1 + 1 + a = double (1 + a) -> 1 + a + 1 = double (1 + 1).
Proof.
move=> a H.
elpi point_run_expect "Simplify here" "rewrite [X in X + _ = _]/=." "" 0 3.
rewrite [X in X + _ = _]/=.
lazymatch goal with |- S a + 1 = double (1 + 1) => idtac end.
elpi point_run_expect "Simplify here" "rewrite [X in _ = double X]/=." "" 12 15.
rewrite [X in _ = double X]/=.
lazymatch goal with |- S a + 1 = double 2 => idtac end.
(* in a hypothesis: rewrite ... in H *)
elpi point_run_expect "Simplify here" "rewrite [X in X + _ = _]/= in H." "" H 0 3.
rewrite [X in X + _ = _]/= in H.
lazymatch goal with H : 2 + a = double (1 + a) |- _ => idtac end.
Abort.

(* ---------- Unfold here ---------- *)

(* double(1+a)=double(double(a)) *)
Goal forall a : nat, double (1 + a) = double (double a) -> double a = a + a.
Proof.
move=> a H.
(* doublea=a+a *)
elpi point_run_expect "Unfold here" "rewrite [X in X = _]/double." "" 0 7.
(* the head of the application selected *)
elpi point_run_expect "Unfold here" "rewrite [X in X _ = _]/double." "" 0 6.
rewrite [X in X = _]/double.
lazymatch goal with |- a + a = a + a => idtac end.
(* the inner double of H *)
elpi point_run_expect "Unfold here" "rewrite [X in _ = double X]/double in H."
  "" H 19 26.
rewrite [X in _ = double X]/double in H.
lazymatch goal with H : double (1 + a) = double (a + a) |- _ => idtac end.
(* + is Nat.add (Init.Nat.add, as Rocq prints it here) *)
elpi point_run_expect "Unfold here" "rewrite [X in X = _]/Init.Nat.add." "" 0 3.
(* a variable is not a constant *)
ltac2:(fails_with "point_run: the selection is not a constant nor an application of a constant"
  (fun () => ltac1:(elpi point_run "Unfold here" 0 1))).
Abort.

(* ---------- Actions declared here ---------- *)

(* by a template *)
PointAction "Name it" point "set x := ({text})." "name the selected subterm".

(* in Elpi: the action is a predicate from the selections to the line *)
Elpi Accumulate pbp_select.db lp:{{
pred same-text i:point-in, o:string.
same-text In Line :-
  point-text In 0 A, point-text In 1 B,
  (A = B, !, Line = "(* the same text *)" ;
   Line is "(* " ^ A ^ " and " ^ B ^ " *)").
point-action "Compare" link "compare the two selections" same-text.
}}.

Goal forall a b : nat, a + b = b + a.
Proof.
move=> a b.
elpi point_actions_expect "[{""name"":""Point"",""kind"":""point"",""doc"":""pbp: bring the selected subformula to the surface of the goal""},{""name"":""Link"",""kind"":""link"",""doc"":""pbp: link the two selected subformulas""},{""name"":""Simplify here"",""kind"":""point"",""doc"":""simplify the selected subterm (ssreflect's rewrite /=, at the selection)""},{""name"":""Unfold here"",""kind"":""point"",""doc"":""unfold the constant at the head of the selected subterm, in it""},{""name"":""Name it"",""kind"":""point"",""doc"":""name the selected subterm""},{""name"":""Compare"",""kind"":""link"",""doc"":""compare the two selections""}]".
elpi point_run_expect "Name it" "set x := (a + b)." "" 0 3.
elpi point_run_expect "Compare" "(* the same text *)" "" 0 1 6 7.
elpi point_run_expect "Compare" "(* a and b *)" "" 0 1 2 3.
set x := (a + b).
lazymatch goal with |- x = b + a => idtac end.
Abort.

(* a doc with characters that JSON escapes *)
PointAction Quote point "idtac." "a ""quoted"" \ doc".
Goal True.
Proof.
elpi point_actions_expect "[{""name"":""Point"",""kind"":""point"",""doc"":""pbp: bring the selected subformula to the surface of the goal""},{""name"":""Link"",""kind"":""link"",""doc"":""pbp: link the two selected subformulas""},{""name"":""Simplify here"",""kind"":""point"",""doc"":""simplify the selected subterm (ssreflect's rewrite /=, at the selection)""},{""name"":""Unfold here"",""kind"":""point"",""doc"":""unfold the constant at the head of the selected subterm, in it""},{""name"":""Name it"",""kind"":""point"",""doc"":""name the selected subterm""},{""name"":""Compare"",""kind"":""link"",""doc"":""compare the two selections""},{""name"":""Quote"",""kind"":""point"",""doc"":""a \""quoted\"" \\ doc""}]".
Abort.

(* ---------- Errors ---------- *)

(* declarations *)
Fail PointAction "Point" point "idtac.".            (* already declared *)
Fail PointAction "P2" pointing "idtac.".            (* no kind pointing *)
Fail PointAction "P3" point "rewrite {patern}.".    (* no placeholder patern *)
Fail PointAction "P4" point "rewrite {pattern.".    (* { not closed *)
Fail PointAction "P5".                              (* no template *)

Goal forall a b : nat, a + b = b + a.
Proof.
move=> a b.
ltac2:(fails_with "point_run: no action Rewrite (elpi point_actions lists them)"
  (fun () => ltac1:(elpi point_run "Rewrite" 0 1))).
ltac2:(fails_with "point_run: the first argument is the name of an action"
  (fun () => ltac1:(elpi point_run 0 1))).
ltac2:(fails_with "point_run: the first argument is the name of an action"
  (fun () => ltac1:(elpi point_run))).
ltac2:(fails_with "point_run: the action Point is of kind point and takes 1 selection(s), not 2"
  (fun () => ltac1:(elpi point_run "Point" 0 1 6 7))).
ltac2:(fails_with "point_run: the action Link is of kind link and takes 2 selection(s), not 1"
  (fun () => ltac1:(elpi point_run "Link" 0 1))).
ltac2:(fails_with "point_run: the range 30 31 is not in the printed term"
  (fun () => ltac1:(elpi point_run "Point" 30 31))).
ltac2:(fails_with "point_run: the range 3 1 ends before it starts"
  (fun () => ltac1:(elpi point_run "Point" 3 1))).
ltac2:(fails_with "point_run: no hypothesis H"
  (fun () => ltac1:(elpi point_run "Point" H 0 1))).
ltac2:(fails_with "point_run: a selection is S E"
  (fun () => ltac1:(elpi point_run "Point" 0))).
ltac2:(fails_with "point_run: the two selections are the same subterm or one is inside the other"
  (fun () => ltac1:(elpi point_run "Link" 0 1 0 3))).
(* the two selections of Simplify here: one action of kind point *)
ltac2:(fails_with "point_run: the action Simplify here is of kind point"
  (fun () => ltac1:(elpi point_run "Simplify here" 0 1 6 7))).
(* pbp_pattern keeps its own name in its messages *)
ltac2:(fails_with "pbp_pattern: the range 30 31 is not in the printed term"
  (fun () => ltac1:(elpi pbp_pattern 30 31))).
Abort.

(* {local} and {in}: the two selections of Compare are in two parts, a
   link action with {local} fails *)
PointAction "Local link" link "idtac {local}{in}.".
Goal forall A : Prop, A -> A.
Proof.
move=> A a.
ltac2:(fails_with "point_run: the selections are not in the same hypothesis or both in the conclusion"
  (fun () => ltac1:(elpi point_run "Local link" a 0 1 0 1))).
Abort.

(* an Elpi action that fails without a message *)
Elpi Accumulate pbp_select.db lp:{{
pred never i:point-in, o:string.
never _ _ :- fail.
point-action "Never" point "" never.
}}.
Goal True.
Proof.
ltac2:(fails_with "point_run: the action Never does not apply to the selection"
  (fun () => ltac1:(elpi point_run "Never" 0 1))).
Abort.
