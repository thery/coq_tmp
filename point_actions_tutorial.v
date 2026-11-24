(* Pointing actions: a tutorial.

   In an interface for proof by pointing (VS Code with vsrocq-pbp, or
   rocq-web), you select a part of the goal with the mouse, and a bar
   below the selection shows one button per pointing action declared at
   that point of the file.  A click writes a line in the script, after the
   sentence the goal is shown for.

   Part 1 uses the two actions of pbp, Point and Link, on a few proofs.
   Part 2 writes two new actions, Simplify here and Unfold here, step by
   step, with all their Elpi code in this file; the bar grows as they
   are declared.

   How to read it: step through it.  Where a button is to be used, a
   comment says what to select, which button to click, and, after an
   arrow, the line the button writes (after a cross, the error the bar
   shows instead).  A comment that starts with "prints" gives the
   messages of the sentence just before it.
   point_actions_tutorial_check.sh checks the arrows, the crosses and the
   messages. *)

From Stdlib Require Import ssreflect.
From coq_tmp Require Import point_actions.

(* ================ Part 1. Point and Link ================

   point_actions.v declares two actions, the ones of pbp.  PointActions
   lists the actions declared at this point: *)
PointActions.
(* prints:
   2 pointing action(s):
   Point (point), declared in coq_tmp.point_actions, line 503
     template: {pre:revert}pbp {path:pbp}{post:revert}.
     doc: pbp: bring the selected subformula to the surface of the goal
   Link (link), declared in coq_tmp.point_actions, line 505
     template: {pre:revert}pbp {path:pbp}{post:revert}.
     doc: pbp: link the two selected subformulas *)

(* Point (one selection) brings the selected formula to the surface of
   the goal: pbp does the logical steps that lead to it.  Link (two
   selections) uses the first one to prove the second one.  In the bar,
   Link… keeps the first selection; select the second one and click
   Link.  A selection in a hypothesis H gives a line that starts with
   move: H; (pbp works on the goal).

   The lines are in the file, so that you can step through the proofs
   first; before each one, a comment says what was selected and clicked.
   Then do it yourself on the copies at the end of this part. *)

Lemma pointing_and (A B : Prop) (ab : A -> B) (a : A) : B /\ A.
Proof.
(* select the B of the conclusion, click "Point": the conjunction is
   split into two goals, B first
   → pbp [X in X /\ _]. *)
pbp [X in X /\ _].
(* select the B in the type of ab (A -> B), click "Link…", then select
   the B of the conclusion and click "Link": B follows from ab, A is left
   → move: ab; pbp [X Y in (_ -> X) -> Y]. *)
move: ab; pbp [X Y in (_ -> X) -> Y].
(* select the A in the type of a, click "Link…", select the conclusion A,
   click "Link": this goal is closed
   → move: a; pbp [X Y in X -> Y]. *)
move: a; pbp [X Y in X -> Y].
(* the second goal, A: select the A of a, click "Link…", select the
   conclusion, click "Link"
   → move: a; pbp [X Y in X -> Y]. *)
move: a; pbp [X Y in X -> Y].
Qed.

Lemma pointing_or (A B : Prop) (h : A \/ B) : B \/ A.
Proof.
(* select the A in the type of h (A \/ B), click "Point": a case
   analysis on h, one goal with X : A, one with pbp : B (pbp names the
   new hypotheses)
   → move: h; pbp [X in X \/ _ -> _]. *)
move: h; pbp [X in X \/ _ -> _].
(* select the A of X, click "Link…", select the A of the conclusion,
   click "Link": A proves the right side of B \/ A
   → move: X; pbp [X0 Y in X0 -> _ \/ Y]. *)
move: X; pbp [X0 Y in X0 -> _ \/ Y].
(* the second goal: select the B of pbp, click "Link…", select the B of
   the conclusion, click "Link"
   → move: pbp; pbp [X Y in X -> Y \/ _]. *)
move: pbp; pbp [X Y in X -> Y \/ _].
Qed.

Lemma pointing_imp (A B C : Prop) : (A -> B) -> (B -> C) -> A -> C.
Proof.
(* select the C of B -> C, click "Link…", select the last C,
   click "Link": the three premises are introduced (pbp, pbp0) and B is left
   → pbp [X Y in _ -> (_ -> X) -> _ -> Y]. *)
pbp [X Y in _ -> (_ -> X) -> _ -> Y].
(* select the B of pbp (A -> B), click "Link…", select the conclusion B,
   click "Link": A is left
   → move: pbp; pbp [X Y in (_ -> X) -> Y]. *)
move: pbp; pbp [X Y in (_ -> X) -> Y].
(* select the A of pbp0, click "Link…", select the conclusion A,
   click "Link": the proof is done
   → move: pbp0; pbp [X Y in X -> Y]. *)
move: pbp0; pbp [X Y in X -> Y].
Qed.

(* Your turn: the same lemmas, no proofs.  Step to Proof, then make the
   clicks above, stepping each line the bar writes ("check" in the bar
   does it for you). *)
Lemma pointing_and_yourself (A B : Prop) (ab : A -> B) (a : A) : B /\ A.
Proof.
Abort.

Lemma pointing_or_yourself (A B : Prop) (h : A \/ B) : B \/ A.
Proof.
Abort.

Lemma pointing_imp_yourself (A B C : Prop) :
  (A -> B) -> (B -> C) -> A -> C.
Proof.
Abort.

(* ================ Part 2. Writing an action ================

   An action is an Elpi predicate: it is given the selection and gives
   the line.  We write two, Simplify here and Unfold here, which change
   the selected subterm only:

   - Simplify here: on the 1 + 1 of 1 + 1 + a = 2 + a, the line is
     rewrite [X in X + _ = _]/=, which computes 1 + 1 and nothing else
     (a plain rewrite /= would change 2 + a too);
   - Unfold here: on double (1 + a), it is rewrite [X in X = _]/double.

   [X in X + _ = _] is ssreflect's pattern: X marks the place of the
   selection, each _ is any term.  The action has to compute it.

   ---- 2a. The action, registered: a constant line ----

   The Elpi code below is added (Elpi Accumulate) to pbp_select.db, the
   database that the interface queries.  It holds:
   - pred simplify-here i:point-in, o:string. declares the predicate, with
     the types and modes of its arguments: an input (i:) of type point-in,
     the selection, and an output (o:), the line;
   - a clause of simplify-here, a fact: for any selection (_), the line
     is "rewrite /=."; :name gives the clause a name, so that the next
     steps can put their clauses before it;
   - a fact of point-action (point_actions.v:69), the register of the
     actions: the name of the button, its kind (point: one selection,
     link: two), a doc (shown when the mouse is on the button), the
     predicate. *)
Elpi Accumulate pbp_select.db lp:{{
pred simplify-here i:point-in, o:string.
:name "simplify-2a"
simplify-here _ "rewrite /=.".
point-action "Simplify here" point "simplify the selected subterm" simplify-here.
}}.

(* The bar now has a third button (a declaration by an Elpi clause is
   listed with its predicate): *)
PointActions.
(* prints:
   3 pointing action(s):
   Point (point), declared in coq_tmp.point_actions, line 503
     template: {pre:revert}pbp {path:pbp}{post:revert}.
     doc: pbp: bring the selected subformula to the surface of the goal
   Link (link), declared in coq_tmp.point_actions, line 505
     template: {pre:revert}pbp {path:pbp}{post:revert}.
     doc: pbp: link the two selected subformulas
   Simplify here (point), declared by an Elpi clause
     Elpi: simplify-here
     doc: simplify the selected subterm *)

(* A click on a button runs elpi point_run with the name and the
   selection, here 0 3: the characters 0 to 3 of the conclusion, blanks
   not counted (the 1 + 1).  It prints the line, and does not change the
   goal. *)
Lemma simplify_2a (a : nat) : 1 + 1 + a = 2 + a.
Proof.
elpi point_run "Simplify here" 0 3.
(* prints: rewrite /=. *)
(* Try it: select 1 + 1, click "Simplify here".
   → rewrite /=. *)
Abort.

(* ---- 2b. Reading the selection ----

   What the action is given, a value of type point-in (pbp_select.v:656),
   has five fields: point-in Names Hs C Parts Ls, where
   - Names are the names of the hypotheses of the goal (the last one
     first);
   - Hs are the hypotheses the selections are in ([] when they are in
     the conclusion);
   - C is the goal with the hypotheses Hs moved into it (what pbp works
     on);
   - Parts are the hypotheses Hs, then the conclusion, each as
     part B T Shs (pbp_select.v:372), T being the term;
   - Ls are the selections, each loc P I P0 (pbp_select.v:387): the path
     P in C, the number I of its part in Parts, the path P0 in that part.
   A path lists the positions of the subterms to go through, from the
   root: in an application, the function is 0 and the arguments 1, 2, ...

   A small tactic that prints these fields for a selection.  A tactic is
   run on a goal, goal Ctx _ Ty _ Args (the hypotheses, the conclusion,
   the arguments of the tactic); [seal G] says that the goal is left as
   it is.  It reads the selection as point_run does (parse-sels,
   pbp_select.v:331; point-resolve, pbp_select.v:666), then matches the
   point-in value against its five fields.  In a clause, :- reads "if",
   a comma "and"; coq.say prints its arguments; coq.term->string T S
   gives the text S of the term T, and {coq.term->string T} is that text
   in place (the braces run the predicate first and put its last
   argument there).  std.forall L P runs P on each element of L; p\ ...
   is a function of p, and sigma T\ ... introduces a variable T local to
   it. *)
Elpi Tactic show_selection.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  parse-sels Args Sels,
  point-resolve Ctx Ty Sels (point-in Names Hs C Parts Ls) _,
  coq.say "Names:" Names,
  coq.say "Hs:" Hs,
  coq.say "C:" {coq.term->string C},
  std.forall Parts (p\ sigma T\ p = part _ T _,
                      coq.say "part:" {coq.term->string T}),
  coq.say "Ls:" Ls.
}}.

(* In the conclusion, the 1 + 1 of 1 + 1 + a = 2 + a: the goal is
   @eq nat (1 + 1 + a) (2 + a), so the left side is at [2], and its first
   argument, 1 + 1, at [2, 1]; there is one part, number 0. *)
Lemma show_2b (a b : nat) (H : 1 + 1 + a = b) : 1 + 1 + a = 2 + a.
Proof.
elpi show_selection 0 3.
(* prints:
   Names: [H, b, a]
   Hs: []
   C: 1 + 1 + a = 2 + a
   part: 1 + 1 + a = 2 + a
   Ls: [loc [2, 1] 0 [2, 1]] *)
(* In the hypothesis H (a selection H S E): H is moved into C, which is
   now an implication, H's type at [1] (in a product, the name is 0, the
   type 1, the body 2); there are two parts, H's type (number 0) and the
   conclusion. *)
elpi show_selection H 0 3.
(* prints:
   Names: [H, b, a]
   Hs: [H]
   C: 1 + 1 + a = b -> 1 + 1 + a = 2 + a
   part: 1 + 1 + a = b
   part: 1 + 1 + a = 2 + a
   Ls: [loc [1, 2, 1] 0 [2, 1]] *)
Abort.

(* The action can now tell where the selection is: in a hypothesis H
   (its part number I is a position in Hs), the line ends with in H.
   The clause matches the selection against point-in _ Hs _ _ [loc _ I _],
   one selection of part I.
   - Elpi tries the clauses of a predicate in order.  :before
     "simplify-2a" puts this clause before the one of 2a, and the cut !
     at the start of its body says: this clause applies, forget the
     others.  So the button runs this clause from now on (each next step
     puts its clause first in the same way).
   - my-where Hs I W gives W, " in H" or "": its first clause applies
     when I is a position in Hs (std.length, then the test I < N), and
     its cut forbids the second clause, which is for the conclusion.
   - S1 ^ S2 puts two strings together, and X is E computes E. *)
Elpi Accumulate pbp_select.db lp:{{
pred my-where i:list string, i:int, o:string.
my-where Hs I W :- std.length Hs N, I < N, !, std.nth I Hs H, W is " in " ^ H.
my-where _ _ "".

:name "simplify-2b" :before "simplify-2a"
simplify-here (point-in _ Hs _ _ [loc _ I _]) Line :- !,
  my-where Hs I W,
  Line is "rewrite /=" ^ W ^ ".".
}}.

Lemma simplify_2b (a b : nat) (H : 1 + 1 + a = b) : b = 2 + a.
Proof.
(* Try it: select the 1 + 1 of H, click "Simplify here".
   → rewrite /= in H. *)
(* Select the 2 + a of the conclusion, click "Simplify here".
   → rewrite /=. *)
Abort.

(* ---- 2c. Walking the term: the pattern ----

   Now the pattern.  The terms of Rocq are, in Elpi, built from a few
   constructors: app [F, A1, ..., An] is F applied to A1 ... An;
   global (const C) a constant, global (indt I) an inductive type;
   prod N A F the product forall x : A, F x (A -> B when F does not use
   x), F being an Elpi function from terms to terms; sort prop is Prop.
   The tactic show_pattern below prints one.

   my-pattern P T X Pat R walks T along the path P: it gives Pat, T where
   the subterm at P, R, is X, the other arguments met on the way being
   holes.  One clause per kind of term:
   - the path [] is T itself: Pat is X, R is T;
   - [N|P] in an application: the function stays, my-args makes the Nth
     argument the pattern of its own subterm and the others holes;
   - in a product, [1|P] goes into the type, the body becomes a hole;
     [2|P] goes into the body (0 is the name of the binder): pi y\ gives a new variable y, the body
     F y is walked, and G, the body of the pattern, is the function that
     gives the result for y.  The type stays when the body uses the
     variable (forall n : nat, ...), else it is a hole (_ -> ...).
   A path into another kind of term (a let, a match) finds no clause:
   my-pattern fails.  So does a selection that uses the variable y of a
   product: R, given outside pi y\, cannot be a term that contains y.

   A hole is pbp_hole (pbp_select.v:45) applied to the subterm it
   replaces: a constant whose arguments are implicit, printed as its name,
   which my-pattern-text then replaces by _ in the text (rex.replace is a
   regular-expression replace).  To print the pattern, X is a new
   variable (pi x\) that the printer is told about (decl x `X` {{ Prop }}
   => ..., the hypothesis X : Prop): {{ ... }} is a Rocq term written in
   Rocq's syntax. *)
Elpi Accumulate pbp_select.db lp:{{
pred my-pattern i:list int, i:term, i:term, o:term, o:term.
my-pattern [] T X X T.
my-pattern [N|P] (app [F|As]) X (app [F|As1]) R :-
  N > 0, M is N - 1, my-args M P As X As1 R.
my-pattern [2|P] (prod Nm A F) X (prod Nm B G) R :-
  my-pattern P A X B R, pi y\ my-hole (F y) (G y).
my-pattern [1|P] (prod Nm A F) X (prod Nm B G) R :-
  my-binder-type A F B, pi y\ my-pattern P (F y) X (G y) R.

% [my-args M P As X Bs R] the argument number M (from 0) of As is
% walked along P, the others are holes
pred my-args i:int, i:list int, i:list term, i:term, o:list term, o:term.
my-args 0 P [A|As] X [B|Hs] R :- !, my-pattern P A X B R, std.map As my-hole Hs.
my-args M P [A|As] X [H|Bs] R :- my-hole A H, M1 is M - 1, my-args M1 P As X Bs R.

pred my-binder-type i:term, i:(term -> term), o:term.
my-binder-type A F A :- pi y\ occurs y (F y), !.
my-binder-type A _ H :- my-hole A H.

pred my-hole i:term, o:term.
my-hole A {{ @pbp_hole Prop lp:A }}.

% [my-pattern-text P T S R] S is the text of the pattern [X in ...] of the
% subterm R of T at path P
pred my-pattern-text i:list int, i:term, o:string, o:term.
my-pattern-text P T S R :-
  pi x\ decl x `X` {{ Prop }} =>
    sigma Pat Txt\ my-pattern P T x Pat R,
                   coq.term->string Pat Txt,
                   rex.replace "pbp_hole" "_" Txt Txt1,
                   S is "[X in " ^ {one-line Txt1} ^ "]".
}}.

(* A tactic to see the walk at work: it prints the pattern as a term of
   Elpi, then as the text the action writes (one-line,
   pbp_select.v:73, puts a text on one line).  In the term, c0 is the
   variable a of the context and c1 the X of the pattern. *)
Elpi Tactic show_pattern.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  parse-sels Args Sels,
  point-resolve Ctx Ty Sels (point-in _ _ _ Parts [loc _ I P0]) _,
  std.nth I Parts (part _ T _),
  (pi x\ decl x `X` {{ Prop }} =>
     sigma Pat R\ my-pattern P0 T x Pat R, coq.say "pattern:" Pat),
  my-pattern-text P0 T S _,
  coq.say "text:" S.
}}.

Lemma show_2c (a : nat) : 1 + 1 = a.
Proof.
elpi show_pattern 0 3.
(* prints:
   pattern: app
    [global (indt «eq»),
     app [global (const «pbp_hole»), sort prop, global (indt «nat»)], c1,
     app [global (const «pbp_hole»), sort prop, c0]]
   text: [X in X = _] *)
Abort.

(* The action, in its part: the conclusion, or the type of H (std.nth I
   Parts gives the part number I). *)
Elpi Accumulate pbp_select.db lp:{{
:name "simplify-2c" :before "simplify-2b"
simplify-here (point-in _ Hs _ Parts [loc _ I P0]) Line :- !,
  my-where Hs I W,
  std.nth I Parts (part _ T _),
  my-pattern-text P0 T Pat _,
  Line is "rewrite " ^ Pat ^ "/=" ^ W ^ ".".
}}.

Lemma simplify_2c (a b : nat) (f : nat -> nat) (H : 1 + 1 + a = b) :
  b = 2 + a /\ forall n, f (0 + n) = f n.
Proof.
(* Try it: select the 1 + 1 of H, click "Simplify here".
   → rewrite [X in X + _ = _]/= in H. *)
(* Select the 2 + a of the conclusion, click "Simplify here".
   → rewrite [X in _ = X /\ _]/=. *)
(* Select the 0 + n of the conclusion, click "Simplify here": it uses
   the n of forall n, my-pattern fails, and so does the action; point_run
   then says so, but not why
   ✗ the action Simplify here does not apply to the selection *)
Abort.

(* ---- 2d. A clear error ----

   An action that cannot write its line says why: coq.ltac.fail 0 M
   stops with the message M, which the bar shows.  msg (pbp_select.v:57)
   puts the name of the tool before it ("point_run: ...").  The
   if-then-else of Elpi: (Cond, ! ; Else) runs Cond and, if it holds,
   keeps its result (the cut); else it runs Else. *)
Elpi Accumulate pbp_select.db lp:{{
:name "simplify-2d" :before "simplify-2c"
simplify-here (point-in _ Hs _ Parts [loc _ I P0]) Line :- !,
  my-where Hs I W,
  std.nth I Parts (part _ T _),
  (my-pattern-text P0 T Pat _, ! ;
   coq.ltac.fail 0 {msg "the selection uses a variable bound in the goal: introduce it first"}),
  Line is "rewrite " ^ Pat ^ "/=" ^ W ^ ".".
}}.

Lemma simplify_2d (a b : nat) (f : nat -> nat) (H : 1 + 1 + a = b) :
  b = 2 + a /\ forall n, f (0 + n) = f n.
Proof.
(* Try it: select the 0 + n again, click "Simplify here".
   ✗ the selection uses a variable bound in the goal: introduce it first *)
(* The rest is as in 2c: select the 2 + a, click "Simplify here".
   → rewrite [X in _ = X /\ _]/=. *)
Abort.

(* ---- 2e. A second action: Unfold here ----

   Unfold here writes rewrite [X in ...]/c, c being the constant the
   selection is an application of: the same pattern, from my-pattern-text,
   whose last output is now used, R the selected subterm.  my-head R C
   walks the applications to their function, a constant global (const C)
   (a variable, a constructor have no clause: my-head fails, and the action
   says so).  The name of C is printed by coq.term->string, which writes
   it as Rocq reads it back (Nat.add for the + of nat), with an @
   before it when it has implicit arguments, removed here. *)
Elpi Accumulate pbp_select.db lp:{{
pred my-head i:term, o:constant.
my-head (global (const C)) C.
my-head (app [F|_]) C :- my-head F C.

pred unfold-here i:point-in, o:string.
unfold-here (point-in _ Hs _ Parts [loc _ I P0]) Line :-
  my-where Hs I W,
  std.nth I Parts (part _ T _),
  (my-pattern-text P0 T Pat R, ! ;
   coq.ltac.fail 0 {msg "the selection uses a variable bound in the goal: introduce it first"}),
  (my-head R C, ! ;
   coq.ltac.fail 0 {msg "the selection is not a constant nor an application of a constant"}),
  coq.term->string (global (const C)) Name0,
  rex.replace "^@" "" Name0 Name,
  Line is "rewrite " ^ Pat ^ "/" ^ Name ^ W ^ ".".
point-action "Unfold here" point "unfold the constant at the head of the selected subterm" unfold-here.
}}.

(* A fourth button: *)
PointActions.
(* prints:
   4 pointing action(s):
   Point (point), declared in coq_tmp.point_actions, line 503
     template: {pre:revert}pbp {path:pbp}{post:revert}.
     doc: pbp: bring the selected subformula to the surface of the goal
   Link (link), declared in coq_tmp.point_actions, line 505
     template: {pre:revert}pbp {path:pbp}{post:revert}.
     doc: pbp: link the two selected subformulas
   Simplify here (point), declared by an Elpi clause
     Elpi: simplify-here
     doc: simplify the selected subterm
   Unfold here (point), declared by an Elpi clause
     Elpi: unfold-here
     doc: unfold the constant at the head of the selected subterm *)

Definition double n := n + n.

Lemma unfold_2e (a : nat) (H : double a = 4) : double (1 + a) = 2 + double a.
Proof.
(* Try it: select double (1 + a), click "Unfold here".
   → rewrite [X in X = _]/double. *)
(* Select the double a of H, click "Unfold here".
   → rewrite [X in X = _]/double in H. *)
(* Select 2 + double a, click "Unfold here": its head is the + of nat.
   → rewrite [X in _ = X]/Nat.add. *)
(* Select the a of H, click "Unfold here": a variable.
   ✗ the selection is not a constant nor an application of a constant *)
Abort.

(* ================ What next ================

   point_actions_more.v declares Simplify here and Unfold here (and Name
   occurrence) for the demos, each in one line, by a template.  On the
   selections above they write the same lines as this file's actions
   (the checker compares them), except on the 0 + n under forall n:
   there, they write [X in _ /\ (forall n : nat, f (X n) = _)], X applied
   to n, where this file's actions refuse.  They also choose a name for X
   that the goal does not use, and check the pattern by reading it back.
   Templates are written with the command PointAction; they are built
   from path methods (where the selection is: a pattern, an occurrence
   number) and hypothesis strategies (how a selection in a hypothesis is
   treated).  The README of this directory (section "Pointing actions")
   describes them and the protocol that the interfaces use. *)
