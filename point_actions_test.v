(* Tests of point_actions.v: the list of the actions (JSON, and PointActions
   for a human reader), the actions declared
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

(* ---------- The actions, for a human reader ---------- *)

(* a command: outside proofs too *)
PointActions.
Elpi point_text_expect actions "5 pointing action(s):
Point (point), declared in coq_tmp.point_actions, line 495
  template: {pre:revert}pbp {path:pbp}{post:revert}.
  doc: pbp: bring the selected subformula to the surface of the goal
Link (link), declared in coq_tmp.point_actions, line 497
  template: {pre:revert}pbp {path:pbp}{post:revert}.
  doc: pbp: link the two selected subformulas
Simplify here (point), declared in coq_tmp.point_actions, line 499
  template: {pre:in}rewrite {local:pbp}/={post:in}.
  doc: simplify the selected subterm (ssreflect's rewrite /=, at the selection)
Unfold here (point), declared in coq_tmp.point_actions, line 501
  template: {pre:in}rewrite {local:pbp}/{head}{post:in}.
  doc: unfold the constant at the head of the selected subterm, in it
Name occurrence (point), declared in coq_tmp.point_actions, line 503
  template: {pre:in}set x := {local:occ}({text}){post:in}.
  doc: name x this occurrence of the selected subterm (ssreflect's set x := {n}(t))".

(* ---------- The list of the actions ---------- *)

Goal True.
Proof.
elpi point_actions.
elpi point_actions_expect "[{""name"":""Point"",""kind"":""point"",""doc"":""pbp: bring the selected subformula to the surface of the goal""},{""name"":""Link"",""kind"":""link"",""doc"":""pbp: link the two selected subformulas""},{""name"":""Simplify here"",""kind"":""point"",""doc"":""simplify the selected subterm (ssreflect's rewrite /=, at the selection)""},{""name"":""Unfold here"",""kind"":""point"",""doc"":""unfold the constant at the head of the selected subterm, in it""},{""name"":""Name occurrence"",""kind"":""point"",""doc"":""name x this occurrence of the selected subterm (ssreflect's set x := {n}(t))""}]".
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
elpi point_run_expect "Name occurrence" "set x := {2}(a)." "" 15 16.
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

(* the two new actions, at the end of the list *)
PointActions.
Elpi point_text_expect actions "7 pointing action(s):
Point (point), declared in coq_tmp.point_actions, line 495
  template: {pre:revert}pbp {path:pbp}{post:revert}.
  doc: pbp: bring the selected subformula to the surface of the goal
Link (link), declared in coq_tmp.point_actions, line 497
  template: {pre:revert}pbp {path:pbp}{post:revert}.
  doc: pbp: link the two selected subformulas
Simplify here (point), declared in coq_tmp.point_actions, line 499
  template: {pre:in}rewrite {local:pbp}/={post:in}.
  doc: simplify the selected subterm (ssreflect's rewrite /=, at the selection)
Unfold here (point), declared in coq_tmp.point_actions, line 501
  template: {pre:in}rewrite {local:pbp}/{head}{post:in}.
  doc: unfold the constant at the head of the selected subterm, in it
Name occurrence (point), declared in coq_tmp.point_actions, line 503
  template: {pre:in}set x := {local:occ}({text}){post:in}.
  doc: name x this occurrence of the selected subterm (ssreflect's set x := {n}(t))
Name it (point), declared in coq_tmp.point_actions_test, line 187
  template: set x := ({text}).
  doc: name the selected subterm
Compare (link), declared by an Elpi clause
  Elpi: same-text
  doc: compare the two selections".

Goal forall a b : nat, a + b = b + a.
Proof.
move=> a b.
elpi point_actions_expect "[{""name"":""Point"",""kind"":""point"",""doc"":""pbp: bring the selected subformula to the surface of the goal""},{""name"":""Link"",""kind"":""link"",""doc"":""pbp: link the two selected subformulas""},{""name"":""Simplify here"",""kind"":""point"",""doc"":""simplify the selected subterm (ssreflect's rewrite /=, at the selection)""},{""name"":""Unfold here"",""kind"":""point"",""doc"":""unfold the constant at the head of the selected subterm, in it""},{""name"":""Name occurrence"",""kind"":""point"",""doc"":""name x this occurrence of the selected subterm (ssreflect's set x := {n}(t))""},{""name"":""Name it"",""kind"":""point"",""doc"":""name the selected subterm""},{""name"":""Compare"",""kind"":""link"",""doc"":""compare the two selections""}]".
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
elpi point_actions_expect "[{""name"":""Point"",""kind"":""point"",""doc"":""pbp: bring the selected subformula to the surface of the goal""},{""name"":""Link"",""kind"":""link"",""doc"":""pbp: link the two selected subformulas""},{""name"":""Simplify here"",""kind"":""point"",""doc"":""simplify the selected subterm (ssreflect's rewrite /=, at the selection)""},{""name"":""Unfold here"",""kind"":""point"",""doc"":""unfold the constant at the head of the selected subterm, in it""},{""name"":""Name occurrence"",""kind"":""point"",""doc"":""name x this occurrence of the selected subterm (ssreflect's set x := {n}(t))""},{""name"":""Name it"",""kind"":""point"",""doc"":""name the selected subterm""},{""name"":""Compare"",""kind"":""link"",""doc"":""compare the two selections""},{""name"":""Quote"",""kind"":""point"",""doc"":""a \""quoted\"" \\ doc""}]".
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

(* ---------- Path methods ---------- *)

(* the path methods of point_actions.v *)
PointPaths.
Elpi point_text_expect paths "Path methods (4), {path:M} or {local:M}:
pbp (Elpi: path-pbp)
  pbp's pattern: [X in X + _ = _] ([X Y in ...] for two selections)
occ (Elpi: path-occ)
  ssreflect's occurrences of the selected term: {2} ({1 3} for two selections of the same term)
at (Elpi: path-at)
  Rocq's occurrences (unfold, pattern ... at n): 2 (1 3 for two)
path (Elpi: path-raw)
  the positions of the selections in the term, from its root (in an application the head is 0 and the arguments 1, 2, ...; in a binder its type is 0 and its body 1): [1, 2] (two lists for two selections)".

(* each method, in the goal ({path:M}) and in the part ({local:M}) *)
PointAction "Paths" point
  "{path:pbp} {local:pbp} {path:occ} {local:occ} {path:at} {local:at} {path:path} {local:path}".
PointAction "Paths 2" link "{path:pbp} {path:occ} {path:at} {path:path}".

(* a+b=b+a, in H and in the conclusion: the first a is 0 1, the last 6 7 *)
Goal forall a b : nat, a + b = b + a -> a + b = b + a.
Proof.
move=> a b H.
elpi point_run_expect "Paths"
  "[X in X + _ = _] [X in X + _ = _] {1} {1} 1 1 [2, 1] [2, 1]" "" 0 1.
elpi point_run_expect "Paths"
  "[X in _ = _ + X] [X in _ = _ + X] {2} {2} 2 2 [3, 2] [3, 2]" "" 6 7.
(* in H: generalized, the goal is H's type -> the conclusion *)
elpi point_run_expect "Paths"
  "[X in X + _ = _ -> _] [X in X + _ = _] {1} {1} 1 1 [0, 2, 1] [2, 1]" "" H 0 1.
elpi point_run_expect "Paths"
  "[X in _ = _ + X -> _] [X in _ = _ + X] {2} {2} 2 2 [0, 3, 2] [3, 2]" "" H 6 7.
(* two selections of the same term: the first a of H, the last of the
   conclusion; no part holds both *)
elpi point_run_expect "Paths 2"
  "[X Y in X + _ = _ -> _ = _ + Y] {1 4} 1 4 [0, 2, 1] [1, 3, 2]" "" H 0 1 6 7.
Abort.

(* the occurrences are the ones of ssreflect and of Rocq: the lines run *)
PointAction "Pattern occurrence" point "{pre:in}pattern {text} at {local:at}{post:in}.".
Goal forall a b : nat, a + b = b + a -> a + b = b + a.
Proof.
move=> a b H.
elpi point_run_expect "Name occurrence" "set x := {2}(a)." "" 6 7.
elpi point_run_expect "Name occurrence" "set x := {2}(a) in H." "" H 6 7.
set x := {2}(a) in H.
lazymatch goal with H : a + b = b + x |- a + b = b + a => idtac end.
elpi point_run_expect "Pattern occurrence" "pattern a at 2." "" 6 7.
pattern a at 2.
lazymatch goal with |- (fun n => a + b = b + n) a => idtac end.
Abort.

(* occurrences under a binder: ssreflect, Rocq and the method count alike *)
(* (forallb:nat,a+b=a)/\a=a *)
Goal forall a : nat, (forall b : nat, a + b = a) /\ a = a.
Proof.
move=> a.
elpi point_run_expect "Name occurrence" "set x := {3}(a)." "" 21 22.
elpi point_run_expect "Pattern occurrence" "pattern a at 4." "" 23 24.
pattern a at 4.
lazymatch goal with |- (fun n => (forall b : nat, a + b = a) /\ a = n) a => idtac end.
simpl.
set x := {3}(a).
lazymatch goal with |- (forall b : nat, a + b = a) /\ x = a => idtac end.
Abort.

(* a method declared here, in Elpi: the depth of the selections *)
Elpi Accumulate pbp_select.db lp:{{
pred path-depth i:point-scope, i:point-in, o:string.
path-depth Sc In S :-
  scope-term Sc In _ Ps,
  std.map Ps (p\ s\ sigma N\ std.length p N, s is int_to_string N) Ss,
  std.string.concat " " Ss S.
point-path "depth" "the depth of the selections" path-depth.
}}.
PointPaths.
Elpi point_text_expect paths "Path methods (5), {path:M} or {local:M}:
pbp (Elpi: path-pbp)
  pbp's pattern: [X in X + _ = _] ([X Y in ...] for two selections)
occ (Elpi: path-occ)
  ssreflect's occurrences of the selected term: {2} ({1 3} for two selections of the same term)
at (Elpi: path-at)
  Rocq's occurrences (unfold, pattern ... at n): 2 (1 3 for two)
path (Elpi: path-raw)
  the positions of the selections in the term, from its root (in an application the head is 0 and the arguments 1, 2, ...; in a binder its type is 0 and its body 1): [1, 2] (two lists for two selections)
depth (Elpi: path-depth)
  the depth of the selections".
PointAction "Depth" point "idtac ""{path:depth} {local:depth}"".".
Goal forall a b : nat, a + b = b + a -> a = a.
Proof.
move=> a b H.
elpi point_run_expect "Depth" "idtac ""3 2""." "" H 0 1.
Abort.

(* errors of the methods *)
Goal forall a b : nat, (forall n : nat, n = a) -> a = b.
Proof.
move=> a b H.
(* foralln:nat,n=a *)
ltac2:(fails_with "point_run: the selection uses a variable bound in the goal: it has no occurrence number"
  (fun () => ltac1:(elpi point_run "Name occurrence" H 12 13))).
ltac2:(fails_with "point_run: the two selections are not the same term"
  (fun () => ltac1:(elpi point_run "Paths 2" 0 1 2 3))).
Abort.
Fail PointAction "Bad" point "{path:nopath}.".   (* no method nopath *)

(* ---------- Hypothesis strategies ---------- *)

PointStrategies.
Elpi point_text_expect strategies "Hypothesis strategies (3), {pre:S} and {post:S}:
revert (Elpi: hyp-revert)
  move the hypotheses to the goal first (move: H; ...), the core acts on the goal
in (Elpi: hyp-in)
  act in the hypothesis itself (... in H)
forward (Elpi: hyp-forward)
  act in a copy of the hypothesis (have H' := H; ... in H'), H stays".

PointAction "Simplify (revert)" point "{pre:revert}rewrite {path:pbp}/={post:revert}.".
PointAction "Simplify (forward)" point "{pre:forward}rewrite {local:pbp}/={post:forward}.".

(* 1+1+a=a *)
Goal forall a : nat, 1 + 1 + a = a -> True.
Proof.
move=> a H.
elpi point_run_expect "Simplify (revert)" "move: H; rewrite [X in X + _ = _ -> _]/=." "" H 0 3.
elpi point_run_expect "Simplify here" "rewrite [X in X + _ = _]/= in H." "" H 0 3.
elpi point_run_expect "Simplify (forward)" "have H' := H; rewrite [X in X + _ = _]/= in H'." "" H 0 3.
have H' := H; rewrite [X in X + _ = _]/= in H'.
lazymatch goal with H : 1 + 1 + a = a, H' : 2 + a = a |- _ => idtac end.
(* H' is taken: the copy is H'0 *)
elpi point_run_expect "Simplify (forward)" "have H'0 := H; rewrite [X in X + _ = _]/= in H'0." "" H 0 3.
(* in the conclusion, the strategies add nothing *)
elpi point_run_expect "Simplify (forward)" "rewrite [X in X]/=." "" 0 4.
move: H; rewrite [X in X + _ = _ -> _]/=.
lazymatch goal with |- 2 + a = a -> True => idtac end.
Abort.

(* a strategy declared here, in Elpi: generalize a copy, H stays *)
Elpi Accumulate pbp_select.db lp:{{
pred hyp-copy i:point-in, o:string, o:string.
hyp-copy In Pre "" :-
  point-hyps In Hs,
  (Hs = [], !, Pre = "" ;
   std.map Hs (h\ s\ s is "(" ^ h ^ ")") Cs, std.string.concat " " Cs S,
   Pre is "move: " ^ S ^ "; ").
point-hyp-strategy "copy" "generalize copies of the hypotheses (move: (H); ...), H stays" hyp-copy.
}}.
PointStrategies.
Elpi point_text_expect strategies "Hypothesis strategies (4), {pre:S} and {post:S}:
revert (Elpi: hyp-revert)
  move the hypotheses to the goal first (move: H; ...), the core acts on the goal
in (Elpi: hyp-in)
  act in the hypothesis itself (... in H)
forward (Elpi: hyp-forward)
  act in a copy of the hypothesis (have H' := H; ... in H'), H stays
copy (Elpi: hyp-copy)
  generalize copies of the hypotheses (move: (H); ...), H stays".
PointAction "Point (copy)" point "{pre:copy}pbp {path:pbp}{post:copy}.".
Goal forall A B : Prop, A /\ B -> A.
Proof.
move=> A B H.
elpi point_run_expect "Point (copy)" "move: (H); pbp [X in X /\ _ -> _]." "" H 0 1.
move: (H); pbp [X in X /\ _ -> _].
(* pbp closes the goal with the A it brings to the surface *)
Qed.

(* errors of the strategies *)
PointAction "Link in" link "idtac{post:in}.".
Goal forall A : Prop, A -> A -> A.
Proof.
move=> A a a'.
(* two hypotheses: not in place *)
ltac2:(fails_with "point_run: the selections are in two places: they cannot be changed in place"
  (fun () => ltac1:(elpi point_run "Link in" a 0 1 a' 0 1))).
Abort.
Fail PointAction "Bad" point "{pre:nostrategy}idtac.".   (* no strategy *)
