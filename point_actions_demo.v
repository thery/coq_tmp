(* Pointing actions: a demo to step through.

   An interface for proof by pointing (VS Code with vsrocq-pbp) shows the
   goal, lets you select a part of it with the mouse and shows, below the
   selection, one button per pointing action declared at that point of
   the file.  Clicking a button writes a line in the script, after the
   sentence the goal is shown for.  The actions are declared in Rocq, in
   any loaded file (point_actions.v declares the first ones); this file
   shows how to declare your own and how to combine them.

   How to read it: step through it.  Before each line that a button
   writes, a comment says what to select and which button to click:

     (* click "Commute here" on 11 14 *)
     rewrite [X in _ = _ + X]Nat.add_comm.

   "on 11 14" is the selection as point_run takes it: the characters 11
   to 14 (14 excluded) of the conclusion, counting the characters that
   are not blanks from 0; "on H 0 3" is a selection in the type of the
   hypothesis H; a link action takes two selections.  In the interface
   you just select with the mouse.  The line after the comment is the
   line the button writes, and it is run here; a line that is only shown
   (another choice for the same goal) is written as a comment.  Outside
   an interface, the same line is printed by

     elpi point_run "Commute here" 11 14.

   (point_actions_demo_check.sh checks that every line of this file is
   the one point_run gives.) *)

From Stdlib Require Import ssreflect PeanoNat Arith Lia ZArith.
From coq_tmp Require Import point_actions.

(* ================ 1. Seeing the state ================ *)

(* The actions declared at this point: name, kind (point: one selection,
   link: two), where it was declared, its template (or the Elpi predicate
   that implements it) and its doc.  point_actions.v declares five: Point
   and Link (pbp), Simplify here, Unfold here, Name occurrence. *)
PointActions.

(* The path methods: how a template writes where the selection is.  pbp
   writes pbp's pattern [X in X + _ = _], occ ssreflect's occurrence {2},
   at Rocq's occurrence 2 (pattern a at 2), path the position in the term
   [3, 2] (for Elpi tools). *)
PointPaths.

(* The hypothesis strategies: how a template acts on a selection in a
   hypothesis H: revert (move: H; then act on the goal), in (act in H:
   ... in H), forward (act in a copy: have H' := H; ... in H'). *)
PointStrategies.

(* ================ 2. Declaring actions from templates ================ *)

(* A template is the line to write, with placeholders that the selection
   fills: {text} the selected subterm as printed, {local:M} where it is in
   its part (the conclusion or the type of its hypothesis) written by the
   path method M, {pre:S} and {post:S} what the strategy S writes before
   and after the core of the line (README, "Pointing actions", lists them
   all). *)

(* No "Commute here" yet: no button, and point_run says so. *)
Goal forall a b c : nat, a + (b + c) = a + (c + b).
Proof.
move=> a b c.
Fail elpi point_run "Commute here" 11 14.
Abort.

(* "Commute here": rewrite with the commutativity of + at the selection,
   in the conclusion, or in the hypothesis H (rewrite ... in H). *)
PointAction "Commute here" point
  "{pre:in}rewrite {local:pbp}Nat.add_comm{post:in}."
  "swap the two sides of the selected sum".

(* Now the button is there.  A plain rewrite Nat.add_comm would swap the
   first sum, a + (b + c); the pattern makes it swap the selected one. *)
Lemma demo_commute (a b c : nat) : a + (b + c) = a + (c + b).
Proof.
(* select c + b, click "Commute here" *)
(* click "Commute here" on 11 14 *)
rewrite [X in _ = _ + X]Nat.add_comm.
by [].
Qed.

(* "Case on this": a case analysis on the selected term, keeping the
   equation E that says which case it is (E must be a fresh name). *)
PointAction "Case on this" point "case E: ({text})."
  "case analysis on the selected term, with the equation E".

Lemma demo_case (n m : nat) : (n <=? m) = true \/ m < n.
Proof.
(* select n <=? m *)
(* click "Case on this" on 1 6 *)
case E: (n <=? m).
- by left.
- by right; apply/Nat.leb_gt.
Qed.

(* "Induction on this": induction on the selected variable (on a compound
   term, the line is not valid ssreflect: section 6 shows how an action
   written in Elpi checks what is selected). *)
PointAction "Induction on this" point "elim: {text}."
  "induction on the selected variable".

Lemma demo_elim (n : nat) : n + 0 = n.
Proof.
(* select the first n *)
(* click "Induction on this" on 0 1 *)
elim: n.
- by [].
- by move=> n /= ->.
Qed.

(* "Generalize this": replace the selected term by a new variable,
   everywhere in the conclusion. *)
PointAction "Generalize this" point "move: ({text})."
  "generalize the selected term".

Lemma demo_generalize (a b : nat) : (a + b) * 2 = a + b + (a + b).
Proof.
(* select the first a + b *)
(* click "Generalize this" on 1 4 *)
move: (a + b).
by move=> n; lia.
Qed.

(* "Name this": name x the selected term, everywhere (Name occurrence,
   declared in point_actions.v, names one occurrence only). *)
PointAction "Name this" point "{pre:in}set x := ({text}){post:in}."
  "name x the selected term (all its occurrences)".

Lemma demo_name (a b : nat) : (a + b) * 2 = a + b + (a + b).
Proof.
(* click "Name occurrence" on 1 4 *)
(* set x := {1}(a + b). *)
(* click "Name this" on 1 4 *)
set x := (a + b).
lia.
Qed.

(* The new actions are at the end of the list. *)
PointActions.

(* ================ 3. The same action, three path methods ================ *)

(* "Where" shows what each path method writes for a selection; it only
   prints (idtac). *)
PointAction "Where" point
  "idtac ""{path:pbp}  {path:occ}  {path:at}  {path:path}""."
  "print where the selection is, in each path method".

(* "Pad" writes the selected number a as 0 + a, in three ways: with pbp's
   pattern, with ssreflect's occurrence, with Rocq's change ... at. *)
PointAction "Pad (pbp)" point
  "{pre:in}rewrite -{local:pbp}(Nat.add_0_l {text}){post:in}."
  "write the selected n as 0 + n (ssreflect rewrite, pbp's pattern)".
PointAction "Pad (occ)" point
  "{pre:in}rewrite -{local:occ}(Nat.add_0_l {text}){post:in}."
  "write the selected n as 0 + n (ssreflect rewrite, occurrence)".
PointAction "Pad (at)" point
  "{pre:in}change {text} with (0 + {text}) at {local:at}{post:in}."
  "write the selected n as 0 + n (Rocq's change, occurrence)".

Lemma demo_paths (a b : nat) : a + b = b + a.
Proof.
(* the first a and the last a: the pattern says where the a is, the
   occurrence says which a it is (the first, the second), the path is the
   position from the root (the 2nd argument of eq, then its 1st or 2nd
   argument, the head being 0) *)
(* click "Where" on 0 1 *)
idtac "[X in X + _ = _]  {1}  1  [2, 1]".
(* click "Where" on 6 7 *)
idtac "[X in _ = _ + X]  {2}  2  [3, 2]".
(* the three methods designate the same a; each line suits its tactic *)
(* click "Pad (occ)" on 6 7 *)
(* rewrite -{2}(Nat.add_0_l a). *)
(* click "Pad (at)" on 6 7 *)
(* change a with (0 + a) at 2. *)
(* click "Pad (pbp)" on 6 7 *)
rewrite -[X in _ = _ + X](Nat.add_0_l a).
(* now a + b = b + (0 + a); the first a, with ssreflect's occurrence *)
(* click "Pad (occ)" on 0 1 *)
rewrite -{1}(Nat.add_0_l a).
(* now 0 + a + b = b + (0 + a); the second b, with Rocq's change *)
(* click "Pad (at)" on 6 7 *)
change b with (0 + b) at 2.
lia.
Qed.

(* The occurrence methods (occ, at) need a selection that does not use a
   variable bound in the goal (the n of forall n, ...): they fail with a
   message there; pbp's pattern names the place itself. *)

(* ================ 4. The same action, three hypothesis strategies ======= *)

(* A selection in a hypothesis H: "Commute here" uses {pre:in} {post:in},
   it changes H in place.  The same core with the two other strategies: *)
PointAction "Commute (forward)" point
  "{pre:forward}rewrite {local:pbp}Nat.add_comm{post:forward}."
  "swap the selected sum, in a copy of its hypothesis".
PointAction "Commute (revert)" point
  "{pre:revert}rewrite {path:pbp}Nat.add_comm{post:revert}."
  "swap the selected sum, after moving its hypothesis to the goal".
(* With revert the path is {path:pbp}, the place in the goal where H is
   moved (H's type -> the conclusion); with in and forward it is
   {local:pbp}, the place in H's type. *)

(* in: when the old H is no longer needed *)
Lemma demo_in (a b c : nat) (H : a + b = c) : c = b + a.
Proof.
(* click "Commute here" on H 0 3 *)
rewrite [X in X = _]Nat.add_comm in H.
by rewrite H.
Qed.

(* forward: when the old H is still needed (H' is a fresh name) *)
Lemma demo_forward (a b c : nat) (H : a + b = c) : c = b + a /\ c = a + b.
Proof.
(* click "Commute (forward)" on H 0 3 *)
have H' := H; rewrite [X in X = _]Nat.add_comm in H'.
by rewrite H' H.
Qed.

(* revert: when one then works on the implication H's type -> goal (to
   rewrite with it, to do an induction that needs H, for pbp) *)
Lemma demo_revert (a b c : nat) (H : a + b = c) : c = b + a.
Proof.
(* click "Commute (revert)" on H 0 3 *)
move: H; rewrite [X in X = _ -> _]Nat.add_comm.
by move=> ->.
Qed.

(* ================ 5. A link action: rewrite with this equation ========== *)

(* The everyday use of two selections: an equation H : l = r and the
   place where to use it.  Select a side of H, then the occurrence of that
   side to replace: the left side l gives rewrite {n}H (l becomes r), the
   right side r gives rewrite -{n}H; n is the number of the occurrence,
   so only the selected one changes.

   A template cannot write it: it has no placeholder for the name of H,
   and it cannot choose the direction from the side selected.  It is
   written in Elpi, as a predicate from the selections (point-in, see
   pbp_select.v) to the line, declared by a clause of point-action. *)
Elpi Accumulate pbp_select.db lp:{{
% [rewrite-eq In Line] Line rewrites with the equation of the first
% selection, at the second selection
pred rewrite-eq i:point-in, o:string.
rewrite-eq (point-in Ns Hs C Parts [L1, L2]) Line :-
  % the first selection is in the hypothesis H, part I1 of the goal (the
  % parts are the hypotheses Hs of the selections, then the conclusion)
  L1 = loc _ I1 P1, std.length Hs NH,
  (I1 < NH, !, std.nth I1 Hs H ;
   coq.ltac.fail 0 "the first selection is not in a hypothesis"),
  std.nth I1 Parts (part _ T1 _),
  % H is an equation l = r and the selection is l (path [2]: the head eq
  % is 0, its type 1, l 2, r 3) or r
  (T1 = app [global EQ, _, Lft, Rgt], coq.locate "eq" EQ, ! ;
   coq.ltac.fail 0 "the hypothesis" H "is not an equation"),
  (P1 = [2], !, Side = Lft, Dir = "" ;
   P1 = [3], !, Side = Rgt, Dir = "-" ;
   coq.ltac.fail 0 "the first selection is not a side of" H),
  % the second selection is that side
  L2 = loc P2 I2 _,
  (term-at P2 C S2, S2 == Side, ! ;
   coq.ltac.fail 0 "the second selection is not the selected side of" H),
  % its occurrence number N in its own part, and where that part is
  occurrences path-part (point-in Ns Hs C Parts [L2]) [N],
  (I2 = NH, !, Where = "" ; std.nth I2 Hs H2, Where is " in " ^ H2),
  Line is "rewrite " ^ Dir ^ "{" ^ int_to_string N ^ "}" ^ H ^ Where ^ ".".
point-action "Rewrite with this equation" link
  "rewrite with the first selection, a side of an equation, at the second"
  rewrite-eq.
}}.

Lemma demo_rewrite (a b : nat) (H : a = b + 1) : a * a = a * (b + 1).
Proof.
(* the right side b + 1 of H, and the b + 1 of the conclusion: *)
(* click "Rewrite with this equation" on H 2 5 7 10 *)
(* rewrite -{1}H. *)
(* the left side a of H, and the second a of the conclusion: *)
(* click "Rewrite with this equation" on H 0 1 2 3 *)
rewrite {2}H.
by [].
Qed.

(* ================ 6. An action written in Elpi: Solve ================ *)

(* "Solve" chooses the tactic from what is selected: the whole conclusion,
   an equation on nat or Z: ring; an order (<, <=, >, >=) on nat or Z:
   lia; a number of type nat or Z (anywhere): ring_simplify on it. *)
Elpi Accumulate pbp_select.db lp:{{
% [ring-type Ty] Ty is a type ring and lia know
pred ring-type i:term.
ring-type {{ nat }}.
ring-type {{ Z }}.

% [order P] P is an order on nat or Z
pred order i:term.
order {{ @le _ _ }}.  order {{ @lt _ _ }}.  order {{ @ge _ _ }}.  order {{ @gt _ _ }}.
order {{ Z.le _ _ }}. order {{ Z.lt _ _ }}. order {{ Z.ge _ _ }}. order {{ Z.gt _ _ }}.

% [solve-line In Line] Line is the tactic for the selection In
pred solve-line i:point-in, o:string.
solve-line (point-in _ Hs C _ [loc P _ _] as In) Line :-
  % the selected subterm T and its type Ty
  (term-at P C T, coq.typecheck T Ty ok, ! ;
   coq.ltac.fail 0 "Solve: the selection uses a bound variable"),
  solve-with Hs P T Ty In Line.

% [solve-with Hs P T Ty In Line] the same, T being at the path P of the
% goal, the hypotheses Hs generalized
pred solve-with i:list string, i:list int, i:term, i:term, i:point-in,
                o:string.
% the whole conclusion (no hypothesis generalized, the path is empty)
solve-with [] [] {{ @eq lp:A _ _ }} _ _ "ring." :- ring-type A, !.
solve-with [] [] T _ _ "lia." :- order T, !.
% a number: ring_simplify it, where it is (" in H" for a hypothesis)
solve-with _ _ _ Ty In Line :- ring-type Ty, !,
  point-text In 0 S, point-in-hyp In W,
  Line is "ring_simplify (" ^ S ^ ")" ^ W ^ ".".
solve-with _ _ _ _ _ _ :-
  coq.ltac.fail 0 "Solve: select the conclusion, an equation or an order, or a number".

point-action "Solve" point
  "ring or lia for the conclusion, ring_simplify for a number" solve-line.
}}.

Lemma demo_ring (a b c : nat) : a * (b + c) = a * c + a * b.
Proof.
(* the left side, a number *)
(* click "Solve" on 0 7 *)
(* ring_simplify (a * (b + c)). *)
(* the whole conclusion, an equation on nat *)
(* click "Solve" on 0 15 *)
ring.
Qed.

Section OnZ.
Local Open Scope Z_scope.

Lemma demo_ringZ (x y : Z) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2.
Proof.
(* click "Solve" on 0 21 *)
ring.
Qed.

Lemma demo_liaZ (x : Z) : x <= x * x + 1 -> x - 1 < x * x + 1.
Proof.
(* Solve acts on the conclusion when it is the whole goal: H first *)
move=> H.
(* click "Solve" on 0 9 *)
lia.
Qed.
End OnZ.

Lemma demo_lia (n : nat) : n < n + 1.
Proof.
(* click "Solve" on 0 5 *)
lia.
Qed.

(* ================ 7. Under the hood ================ *)

(* ---- (a) A tactic of your own, made pointable ----

   The tactic: [zero_left [X in C]] writes the number at the place X of
   the goal as 0 + it.  It takes a pattern, as pbp does: [X in C] is the
   notation of pbp.v for fun X => C (here _ are holes), so a pointing
   action can give it the pattern of the selection. *)
Elpi Tactic zero_left_tac.
Elpi Accumulate lp:{{
solve (goal _ _ Ty _ [trm P] as G) GL :-
  % P is fun X => C; Y is what X is in the goal: P Y is the goal
  coq.unify-eq {{ lp:P lp:Y }} Ty ok,
  P = fun _ _ F,
  % the new goal is C with 0 + Y at X (the same up to computation)
  refine {{ (_ : lp:{{ F {{ 0 + lp:Y }} }}) }} G GL.
}}.
Tactic Notation "zero_left" uconstr(t) := elpi zero_left_tac ltac_term:(t).

(* The action: a predicate from the selection to the line, declared by a
   clause of point-action (name, kind, doc, predicate).  The helpers of
   pbp_select.v give the pieces: point-pattern the pattern [X in ...] in
   the goal where the hypotheses of the selection are moved (as pbp's),
   point-revert the move: H; that moves them; also point-local-pattern
   (the pattern in the part itself), point-in-hyp ( in H), point-text
   (the selected text), point-head (its head constant). *)
Elpi Accumulate pbp_select.db lp:{{
pred zero-left-line i:point-in, o:string.
zero-left-line In Line :-
  % the selection is at the path P of the goal C (hypotheses moved)
  In = point-in _ _ C _ [loc P _ _],
  % the action applies to numbers only: say so otherwise
  (term-at P C T, coq.typecheck T {{ nat }} ok, ! ;
   coq.ltac.fail 0 "Zero left: the selection is not a number of type nat"),
  point-revert In Pre,     % "move: H; " for a selection in H, "" otherwise
  point-pattern In Pat,    % "[X in X = _]"
  Line is Pre ^ "zero_left " ^ Pat ^ ".".
point-action "Zero left" point "write the selected number n as 0 + n"
  zero-left-line.
}}.

(* The button "Zero left" is now there; PointActions shows it as declared
   by an Elpi clause, with its predicate zero-left-line. *)
PointActions.

Lemma demo_zero (a b : nat) (H : a + b = b) : a = 0.
Proof.
(* the whole conclusion is not a number *)
Fail elpi point_run "Zero left" 0 3.
(* click "Zero left" on 0 1 *)
zero_left [X in X = _].
(* in a hypothesis: moved first, as for pbp *)
(* click "Zero left" on H 0 1 *)
move: H; zero_left [X in X + _ = _ -> _].
lia.
Qed.

(* ---- (b) How pbp is hooked ----

   pbp is a tactic of pbp.v that knows nothing of selections: [pbp [X in
   C]] takes a pattern of the goal that marks one subformula X, and does
   the logical steps (intro, split, apply, ...) that bring X to the
   surface of the goal; [pbp [X Y in C]] marks two, and uses X to prove
   Y.  It is hooked into the pointing actions exactly as zero_left is,
   with a template instead of an Elpi predicate:

(* point_actions.v, lines 495-498:
PointAction "Point" point "{pre:revert}pbp {path:pbp}{post:revert}."
  "pbp: bring the selected subformula to the surface of the goal".
PointAction "Link" link "{pre:revert}pbp {path:pbp}{post:revert}."
  "pbp: link the two selected subformulas".
*)

   {path:pbp} is the path method pbp, a clause of point-path: in the goal
   (path-goal) it is the pattern that point-pattern builds, in the part
   (path-part) the one of point-local-pattern:

(* point_actions.v, lines 132-134:
pred path-pbp i:point-scope, i:point-in, o:string.
path-pbp path-goal In S :- point-pattern In S.
path-pbp path-part In S :- point-local-pattern In S.
*)
(* point_actions.v, line 149:
point-path "pbp" "pbp's pattern: [X in X + _ = _] ([X Y in ...] for two selections)" path-pbp.
*)

   {pre:revert} and {post:revert} are the strategy revert, a clause of
   point-hyp-strategy: before the core it writes what point-revert gives,
   after it nothing:

(* point_actions.v, lines 173-174:
pred hyp-revert i:point-in, o:string, o:string.
hyp-revert In Pre "" :- point-revert In Pre.
*)
(* point_actions.v, line 186:
point-hyp-strategy "revert" "move the hypotheses to the goal first (move: H; ...), the core acts on the goal" hyp-revert.
*)
(* pbp_select.v, lines 512-515:
pred point-revert i:point-in, o:string.
point-revert (point-in _ [] _ _ _) "" :- !.
point-revert (point-in _ Hs _ _ _) M :-
  std.string.concat " " Hs HsS, M is "move: " ^ HsS ^ "; ".
*)

   The flow, for a selection of A in H : A /\ B:
   1. the interface sends the selection, H 0 1: the characters 0 to 1 of
      the type of H, blanks not counted (elpi point_run "Point" H 0 1);
   2. pbp_select.v resolves it to a subterm of the goal where H is moved,
      A /\ B -> B /\ A: the A at the path [0, 1], in the part H;
   3. the path method pbp writes where it is: [X in X /\ _ -> _];
   4. the strategy revert writes what comes before: move: H;
   5. the template puts the pieces together: move: H; pbp [X in X /\ _ ->
      _]. (the "Pieces" action below shows them one by one);
   6. the interface inserts the line in the script, and Rocq runs it:
      pbp does the proof step.
   To hook your own tactic: give it an argument that a path method writes
   (a pattern, an occurrence, a path), then declare an action whose line
   calls it, by a template or by an Elpi predicate. *)
PointAction "Pieces" point
  "idtac ""pre=[{pre:revert}] path=[{path:pbp}] post=[{post:revert}]""."
  "print the pieces of the line of Point".

Lemma demo_pbp (A B : Prop) (H : A /\ B) : B /\ A.
Proof.
(* click "Pieces" on H 0 1 *)
idtac "pre=[move: H; ] path=[[X in X /\ _ -> _]] post=[]".
(* click "Point" on H 0 1 *)
move: H; pbp [X in X /\ _ -> _].
(* pbp gave the two parts of H, pbp : B and X : A *)
by split.
Qed.
