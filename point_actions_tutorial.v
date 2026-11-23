(* Pointing actions: a tutorial, centred on their Elpi code.

   In an interface for proof by pointing (VS Code with vsrocq-pbp, or
   rocq-web), you select a part of the goal with the mouse, and a bar
   below the selection shows one button per pointing action declared at
   that point of the file.  A click writes a line in the script, after the
   sentence the goal is shown for.  This file shows how this works inside,
   what you can change, and how to write your own pieces in Elpi.

   How to read it: step through it.  Each section shows real code (the
   quoted excerpts are verbatim: point_actions_tutorial_check.sh checks
   them) and ends with something to try.  Where a button is to be used, a
   comment says what to select, which button to click, and, after an
   arrow, the line the button writes (after a cross, the error the bar
   shows instead).  The line is not in the file: the file compiles
   without any click, and each try ends with Abort.  After the click,
   step the new line to see what it does.

   1. The pipeline: from the mouse to the line
   2. The parametrized pieces: actions, templates, path methods,
      hypothesis strategies
   3. Writing your own pieces in Elpi
   4. Templates, a short-hand for Elpi actions
   5. How pbp is hooked, and how to hook your own tactic *)

From Stdlib Require Import ssreflect PeanoNat Arith Lia.
From coq_tmp Require Import point_actions.

(* ================ 1. The pipeline ================

     you select "c + b" in        a + (b + c) = a + (c + b)
         |
         |  the interface sends the selection as a range of characters
         |  of the printed goal, blanks not counted: 11 to 14
         v
     pbp_select.v (point-resolve) finds which part it is in (the
         |  conclusion, or the type of a hypothesis H), the subterm it
         |  is (c + b), and its path in the goal
         v
     a value of type point-in, given to the action
         |
         |  the action, an Elpi predicate  pred i:point-in, o:string,
         |  builds the line
         v
     "set x := {1}(c + b)."  which the interface inserts in the script

   The interface does all this with one tactic call, which does not change
   the goal and prints the line:

     elpi point_run "Name occurrence" 11 14.

   The value of type point-in is the heart of the design: it is all an
   action knows about the selection.  Its declaration: *)
(* pbp_select.v, lines 443-448:
kind point-in type.
% [point-in Names Hs C Parts Ls] selections in a goal: Names are the
% names of its hypotheses, Hs the hypotheses the selections are in (generalized, in the order of the context), C the goal with
% Hs generalized, Parts its parts, Ls the selections (in the order given)
type point-in list string -> list string -> term -> list part -> list loc ->
              point-in.
*)
(* - Names: the names of all the hypotheses of the goal (to choose fresh
     names);
   - Hs: the hypotheses that the selections are in ([] when the
     selections are in the conclusion);
   - C: the goal with the hypotheses Hs generalized: for a selection in
     H : a + b = c, C is a + b = c -> (the conclusion).  pbp works on C;
   - Parts: the hypotheses Hs, then the conclusion, each as a part;
   - Ls: the selections, in the order they were made (one for an action
     of kind point, two for a link).

   A part and a selection: *)
(* pbp_select.v, lines 307-310:
kind part type.
% [part B T Shs] a part of the generalized goal: the hypothesis or the
% conclusion T at path B, its subterms printed as Shs (paths from T)
type part list int -> term -> list shown -> part.
*)
(* pbp_select.v, lines 322-326:
kind loc type.
% [loc P I P0] a selection: the subterm at path P of the generalized goal,
% in its part number I (the hypotheses, then the conclusion), at path P0 of
% that part
type loc list int -> int -> list int -> loc.
*)
(* A path lists the positions of the immediate subterms to go through,
   from the root: in an application the head is 0 and the arguments 1, 2,
   ...; in a product or an abstraction the type is 0 and the body 1.  In
   [a + (b + c) = a + (c + b)], that is [@eq nat (a + (b + c)) (a + (c +
   b))], the right side is at [3], and c + b at [3, 2].

   The printed subterms of a part, the ones that can be selected: *)
(* pbp_select.v, lines 170-173:
kind shown type.
% [shown P S E T] the subterm at path P is printed from the character S
% (included) to E (excluded), and its text without blanks is T
type shown list int -> int -> int -> string -> shown.
*)
(* elpi point_show (defined at the end of point_actions.v for this
   tutorial) prints the point-in value for a selection, field by field,
   with the printed subterms of each part: step the lines below and read
   the output.  The selection 11 14 lies inside the printed subterm
   (c+b), from 10 to 15, and is exactly the subterm c+b at [3, 2]; "in
   Elpi" is the subterm as the action sees it (c0, c1, c2 are the
   variables a, b, c of the context). *)
Lemma pipeline (a b c : nat) : a + (b + c) = a + (c + b).
Proof.
elpi point_show 11 14.
elpi point_run "Name occurrence" 11 14.
(* Try it: select the c + b on the right, click "Name occurrence".
   → set x := {1}(c + b). *)
Abort.

(* In a hypothesis, the selection is H S E.  Now Hs = [H], C is the goal
   with H generalized, and there are two parts: the type of H, at [0] of
   C, and the conclusion, at [1]. *)
Lemma pipeline_hyp (a b c : nat) (H : a + b = c) : c = b + a.
Proof.
elpi point_show H 0 3.
(* Try it: select the a + b of H, click "Name occurrence".
   → set x := {1}(a + b) in H. *)
Abort.

(* ================ 2. The parametrized pieces ================

   Four things are open, each an Elpi predicate of the database
   pbp_select.db to which any file can add clauses: the actions
   (point-action), the path methods (point-path), the hypothesis
   strategies (point-hyp-strategy), and, through the PointAction command,
   the templates.  Fixed: how a selection becomes a point-in value
   (pbp_select.v), the type point-in itself, the syntax of the templates
   and their fixed placeholders ({head}, {text}), and the protocol of the
   interfaces (elpi point_actions, elpi point_run).

   ---- 2a. The actions ----

   An action is a clause of point-action: *)
(* point_actions.v, lines 62-65:
% [point-action Name Kind Doc Impl] the action Name, of kind Kind,
% described by Doc, gives the line Impl In Line for the selections In
pred point-action o:string, o:point-kind, o:string,
                  o:(pred i:point-in, o:string).
*)
(* Its last argument is the predicate that builds the line.  The
   interface asks for the list (elpi point_actions prints it as JSON) and
   runs one with point_run, whose core is: *)
(* point_actions.v, lines 315-324:
point-run Ctx G [str Name | As] Line Ws :- !,
  (point-action Name K _ Impl, ! ;
   coq.ltac.fail 0 {msg "no action"} Name "(elpi point_actions lists them)"),
  parse-sels As Sels, std.length Sels N, point-kind-name K KS KN,
  (N = KN, ! ;
   coq.ltac.fail 0 {msg "the action"} Name "is of kind" KS "and takes" KN
     "selection(s), not" N),
  point-resolve Ctx G Sels In Ws,
  (Impl In Line, ! ;
   coq.ltac.fail 0 {msg "the action"} Name "does not apply to the selection").
*)
(* It finds the first clause of point-action with that name, reads the
   selections (parse-sels), checks their number against the kind,
   resolves them into a point-in value In (point-resolve, section 1), and
   calls the action: Impl In Line.

   PointAction "Name" Kind "Template" "Doc" checks its arguments and adds
   one clause, whose predicate is point-template applied to the template
   (and one clause of point-action-origin, to say where it was declared):
*)
(* point_actions.v, lines 352-355:
  coq.elpi.accumulate _ "pbp_select.db"
    (clause _ _ (point-action Name Kind Doc (point-template T))),
  coq.elpi.accumulate _ "pbp_select.db"
    (clause _ _ (point-action-origin Name Lib Line)).
*)
(* The actions declared at this point (five, by point_actions.v): *)
PointActions.

(* ---- 2b. Templates ----

   A template is the line to write, with placeholders between braces.  It
   is cut into text and placeholders, of type tpart: *)
(* point_actions.v, lines 192-194:
kind tpart type.
type tlit string -> tpart.    % a text
type thole string -> tpart.   % a placeholder {name}
*)
(* For instance (Elpi Query runs a query in the program of a command, here
   PointActions, which holds pbp_select.db): *)
Elpi Query PointActions lp:{{
  tpl-parse "{pre:in}rewrite {local:pbp}/={post:in}." Ps
}}.
(* Then point-template replaces each placeholder by its value for the
   selections, and puts the pieces together: *)
(* point_actions.v, lines 262-267:
% [point-template T In Line] Line is the template T for the selections In
pred point-template i:string, i:point-in, o:string.
point-template T In Line :-
  tpl-parse T Ps,
  std.map Ps (p\ s\ (p = tlit s ; sigma N\ p = thole N, placeholder-value N In s)) Ss,
  std.string.concat "" Ss Line.
*)
(* The value of a placeholder: {head} and {text} are fixed; the others
   name a path method or a strategy, looked up by name in its predicate
   and called (the cut ! after the look-up takes the first clause of that
   name): *)
(* point_actions.v, lines 248-260:
placeholder-value "head" In V :- !,
  (point-head In 0 (const C), ! ;
   coq.ltac.fail 0 {msg "the selection is not a constant nor an application of a constant"}),
  coq.term->string (global (const C)) V0, rex.replace "^@" "" V0 V.
placeholder-value "text" In V :- !, point-text In 0 V.
placeholder-value N In V :- prefixed "path:" N M, !,
  point-path M _ Impl, !, Impl path-goal In V.
placeholder-value N In V :- prefixed "local:" N M, !,
  point-path M _ Impl, !, Impl path-part In V.
placeholder-value N In V :- prefixed "pre:" N S, !,
  point-hyp-strategy S _ Impl, !, Impl In V _.
placeholder-value N In V :- prefixed "post:" N S, !,
  point-hyp-strategy S _ Impl, !, Impl In _ V.
*)
(* So {local:pbp} calls the path method "pbp" in the scope path-part, and
   {pre:in} the strategy "in", whose first output is what comes before.
   A template cannot use a method or a strategy that is not declared:
   PointAction checks it (placeholder, lines 228-231). *)

(* ---- 2c. Path methods ----

   A path method writes where the selections are, in the form a tactic
   reads.  It is given a scope: *)
(* point_actions.v, lines 76-86:
kind point-scope type.
type path-goal point-scope.   % in the goal where the hypotheses of the
                              % selections are generalized
type path-part point-scope.   % in their own part: the conclusion, or the
                              % type of their hypothesis

% [point-path Name Doc Impl] the path method Name, described by Doc, writes
% Impl Scope In S for the selections In, in the scope Scope (or fails
% with a message)
pred point-path o:string, o:string,
                o:(pred i:point-scope, i:point-in, o:string).
*)
(* The methods pbp and occ: *)
(* point_actions.v, lines 132-137:
pred path-pbp i:point-scope, i:point-in, o:string.
path-pbp path-goal In S :- point-pattern In S.
path-pbp path-part In S :- point-local-pattern In S.

pred path-occ i:point-scope, i:point-in, o:string.
path-occ Sc In S :- occurrences Sc In Ns, ints-text Ns T, S is "{" ^ T ^ "}".
*)
(* point_actions.v, lines 149-150:
point-path "pbp" "pbp's pattern: [X in X + _ = _] ([X Y in ...] for two selections)" path-pbp.
point-path "occ" "ssreflect's occurrences of the selected term: {2} ({1 3} for two selections of the same term)" path-occ.
*)
(* pbp's pattern is built by point-pattern and point-local-pattern of
   pbp_select.v; occ calls occurrences (lines 106-121), which counts the
   subterms equal to the selected one, left to right, in the term of the
   scope, as ssreflect's {n} counts them.  Two helpers that a method of
   your own can use: scope-term Sc In T Ps (T is the term of the scope,
   Ps the paths of the selections in it) and term-at P T R (R is the
   subterm of T at path P). *)
PointPaths.

(* A template that prints what each method writes (in a Rocq string, a
   double quote is written twice): *)
PointAction "Where" point
  "idtac ""{path:pbp}  {path:occ}  {path:at}  {path:path}""."
  "print where the selection is, in each path method".

Lemma try_paths (a b : nat) : a + b = b + a.
Proof.
(* Try it: select the first a, click "Where".
   → idtac "[X in X + _ = _]  {1}  1  [2, 1]". *)
(* Then select the last a, click "Where".
   → idtac "[X in _ = _ + X]  {2}  2  [3, 2]". *)
Abort.

(* ---- 2d. Hypothesis strategies ----

   For a selection in a hypothesis H, a strategy writes what comes before
   the core of the line and what comes after it (before its final dot);
   for selections in the conclusion it writes nothing: *)
(* point_actions.v, lines 158-162:
% [point-hyp-strategy Name Doc Impl] the strategy Name, described by Doc,
% writes Impl In Pre Post around the core of the line, for the selections
% In (or fails with a message)
pred point-hyp-strategy o:string, o:string,
                        o:(pred i:point-in, o:string, o:string).
*)
(* revert moves the hypotheses to the goal (the core then acts on C, so
   it goes with {path:M}); in acts in H itself (with {local:M}); one-hyp
   checks that the selections are in one place: *)
(* point_actions.v, lines 164-177:
% [one-hyp In H] the selections are in the hypothesis H, or in the
% conclusion (H = "")
pred one-hyp i:point-in, o:string.
one-hyp In H :-
  point-hyps In Hs,
  (Hs = [], !, H = "" ;
   Hs = [H0], point-part In _, !, H = H0 ;
   coq.ltac.fail 0 {msg "the selections are in two places: they cannot be changed in place"}).

pred hyp-revert i:point-in, o:string, o:string.
hyp-revert In Pre "" :- point-revert In Pre.

pred hyp-in i:point-in, o:string, o:string.
hyp-in In "" Post :- one-hyp In H, (H = "", !, Post = "" ; Post is " in " ^ H).
*)
(* point_actions.v, lines 186-188:
point-hyp-strategy "revert" "move the hypotheses to the goal first (move: H; ...), the core acts on the goal" hyp-revert.
point-hyp-strategy "in" "act in the hypothesis itself (... in H)" hyp-in.
point-hyp-strategy "forward" "act in a copy of the hypothesis (have H' := H; ... in H'), H stays" hyp-forward.
*)
PointStrategies.

(* The same core, rewrite at the selection with /=, with the three
   strategies (Simplify here, of point_actions.v, uses in): *)
PointAction "Simplify (revert)" point "{pre:revert}rewrite {path:pbp}/={post:revert}."
  "simplify the selected subterm, after moving its hypothesis to the goal".
PointAction "Simplify (forward)" point "{pre:forward}rewrite {local:pbp}/={post:forward}."
  "simplify the selected subterm, in a copy of its hypothesis".

Lemma try_strategies (a b : nat) (H : 1 + 1 + a = b) : b = a + 2.
Proof.
(* Try it: select the 1 + 1 of H, click "Simplify here".
   → rewrite [X in X + _ = _]/= in H. *)
(* Or click "Simplify (forward)": H stays, H' is the new one.
   → have H' := H; rewrite [X in X + _ = _]/= in H'. *)
(* Or click "Simplify (revert)": the pattern is in C, where H's type is
   on the left of an implication.
   → move: H; rewrite [X in X + _ = _ -> _]/=. *)
Abort.

(* ================ 3. Writing your own pieces in Elpi ================

   Each piece is a predicate added to pbp_select.db by Elpi Accumulate,
   and one clause that registers it under a name.  An error is
   coq.ltac.fail 0 {msg "..."}: msg adds the name of the tool
   (point_run: ...), and the interface shows the message.

   ---- 3a. A path method: the other copies ----

   ssreflect's occurrence switch {-n} selects all the copies of a term
   but the n-th.  The method "others" writes it for the selection: it
   reuses occurrences for the number, and counts the copies to give a
   clear error when there is no other one. *)
Elpi Accumulate pbp_select.db lp:{{
pred path-others i:point-scope, i:point-in, o:string.
path-others Sc In S :-
  occurrences Sc In Ns,                  % the selection is copy number Ns
  scope-term Sc In T [P|_], term-at P T R,   % R: the selected term
  std.findall (path-of T Q_) All,        % all the subterms of T ...
  std.filter All (c\ sigma Q R1\ c = path-of T Q, term-at Q T R1, R1 == R)
    Copies,                              % ... that are copies of R
  std.length Copies K, std.length Ns KN,
  (K > KN, ! ;
   coq.ltac.fail 0 {msg "the selected term has no other copy"}),
  ints-text Ns Txt, S is "{-" ^ Txt ^ "}".
point-path "others" "ssreflect's occurrences of the other copies of the selected term: {-2}" path-others.
}}.

(* Used at once in a template (2b): *)
PointAction "Name the others" point
  "{pre:in}set x := {local:others}({text}){post:in}."
  "name x all the copies of the selected term but this one".

Lemma try_others (a : nat) : 2 * a = a + a.
Proof.
(* Try it: select the a of 2 * a, click "Name the others".
   → set x := {-1}(a). *)
(* Select the 2 instead and click "Name the others": the 2 has no other
   copy, and the bar shows the error
   ✗ the selected term has no other copy *)
Abort.

(* ---- 3b. A hypothesis strategy: around ----

   revert moves H to the goal and leaves it there; in needs a tactic that
   has an "in H" form, and one hypothesis.  "around" moves the hypotheses
   to the goal, lets the core act there, then brings them back under
   their names: for any tactic, and for selections in several
   hypotheses.  It reuses point-revert of pbp_select.v (lines 510-515),
   the helper of revert. *)
Elpi Accumulate pbp_select.db lp:{{
pred hyp-around i:point-in, o:string, o:string.
hyp-around In Pre Post :-
  point-revert In Pre,              % "move: H; " ("" in the conclusion)
  point-hyps In Hs,                 % [H]
  (Hs = [], !, Post = "" ;
   std.string.concat " " Hs S, Post is "; move=> " ^ S).
point-hyp-strategy "around" "move the hypotheses to the goal, act there, then bring them back: move: H; ...; move=> H" hyp-around.
}}.

PointAction "Commute (around)" point
  "{pre:around}rewrite {path:pbp}Nat.add_comm{post:around}."
  "swap the selected sum, its hypothesis moved to the goal and back".

Lemma try_around (a b c : nat) (H : a + b = c) : b + a = c.
Proof.
(* Try it: select the a + b of H, click "Commute (around)".
   → move: H; rewrite [X in X = _ -> _]Nat.add_comm; move=> H. *)
Abort.

PointStrategies.

(* ---- 3c. Actions that look at the selection ----

   A template writes the same line for any selection.  An action written
   in Elpi can look at what is selected, refuse with a clear message, and
   choose its line.

   "Induction on this" writes elim: n, only if the selection is a
   variable n of the context whose type is an inductive type.  It reads
   the fields of point-in: C and the path P of the one selection. *)
Elpi Accumulate pbp_select.db lp:{{
pred induction-line i:point-in, o:string.
induction-line (point-in _ _ C _ [loc P _ _]) Line :-
  % T: the selected subterm (term-at fails under a binder of the goal)
  (term-at P C T, ! ;
   coq.ltac.fail 0 {msg "the selection uses a variable bound in the goal: introduce it first"}),
  % a variable of the context is an Elpi name with a decl
  (name T, decl T N Ty, ! ;
   coq.ltac.fail 0 {msg "the selection is not a variable (elim: needs one)"}),
  (coq.safe-dest-app Ty (global (indt _)) _, ! ;
   coq.ltac.fail 0 {msg "the type of the selection is not an inductive type"}),
  coq.name->id N X,
  Line is "elim: " ^ X ^ ".".
point-action "Induction on this" point "induction on the selected variable" induction-line.
}}.

Lemma try_induction (n : nat) : n + 0 = n.
Proof.
(* Try it: select the first n, click "Induction on this".
   → elim: n. *)
(* Select n + 0 instead and click "Induction on this": the bar shows
   the error
   ✗ the selection is not a variable (elim: needs one) *)
Abort.

(* "Rewrite with this equation", a link action (two selections): select
   a side of an equation H : l = r, then the copy of it to replace.  The
   left side gives rewrite {n}H (l becomes r), the right side rewrite
   -{n}H.  The number n is not computed here: the action calls the path
   method occ through its registry, on the second selection alone. *)
Elpi Accumulate pbp_select.db lp:{{
pred rewrite-eq i:point-in, o:string.
rewrite-eq (point-in Ns Hs C Parts [L1, L2]) Line :-
  % the first selection is in the hypothesis H, the part I1 (the parts
  % are the hypotheses Hs of the selections, then the conclusion)
  L1 = loc _ I1 P1, std.length Hs NH,
  (I1 < NH, !, std.nth I1 Hs H ;
   coq.ltac.fail 0 {msg "select first a side of an equation in a hypothesis"}),
  std.nth I1 Parts (part _ T1 _),
  % H is l = r (@eq A l r: eq is at 0, A at 1, l at 2, r at 3)
  (T1 = app [global EQ, _, Lft, Rgt], coq.locate "eq" EQ, ! ;
   coq.ltac.fail 0 {msg "the hypothesis"} H "is not an equation"),
  (P1 = [2], !, Side = Lft, Dir = "" ;
   P1 = [3], !, Side = Rgt, Dir = "-" ;
   coq.ltac.fail 0 {msg "the first selection is not a side of"} H),
  % the second selection is a copy of that side
  L2 = loc P2 I2 _,
  (term-at P2 C S2, S2 == Side, ! ;
   coq.ltac.fail 0 {msg "the second selection is not the selected side of"} H),
  % its occurrence, by the path method occ, in its own part
  point-path "occ" _ Occ, !, Occ path-part (point-in Ns Hs C Parts [L2]) N,
  (I2 = NH, !, Where = "" ; std.nth I2 Hs H2, Where is " in " ^ H2),
  Line is "rewrite " ^ Dir ^ N ^ H ^ Where ^ ".".
point-action "Rewrite with this equation" link
  "rewrite with the first selection, a side of an equation, at the second"
  rewrite-eq.
}}.

Lemma try_rewrite_eq (a b : nat) (H : a = b + 1) : a * a = a * (b + 1).
Proof.
(* Try it: select the b + 1 of H, click "Rewrite with this equation…",
   select the b + 1 of the conclusion, click "Rewrite with this equation".
   → rewrite -{1}H. *)
(* Or: select the a of H, click "Rewrite with this equation…", select the
   second a of the conclusion, click "Rewrite with this equation".
   → rewrite {2}H. *)
Abort.

(* The actions written in Elpi are listed with their predicate: *)
PointActions.

(* ================ 4. Templates, a short-hand ================

   A template is an Elpi action whose predicate is point-template applied
   to the template (2a).  The clause that PointAction adds for "Commute
   here" below is the answer of the query after it: *)
PointAction "Commute here" point
  "{pre:in}rewrite {local:pbp}Nat.add_comm{post:in}."
  "swap the two sides of the selected sum".
Elpi Query PointActions lp:{{
  point-action "Commute here" Kind Doc Impl
}}.

(* point-template does, for this template, what this action does by hand
   (2b): the strategy "in" before and after, the method "pbp" in the part
   between, each looked up by name: *)
Elpi Accumulate pbp_select.db lp:{{
pred commute-here i:point-in, o:string.
commute-here In Line :-
  point-hyp-strategy "in" _ Strat, !, Strat In Pre Post,
  point-path "pbp" _ Path, !, Path path-part In P,
  Line is Pre ^ "rewrite " ^ P ^ "Nat.add_comm" ^ Post ^ ".".
point-action "Commute here (Elpi)" point "the same as Commute here, by hand" commute-here.
}}.

(* The two give the same line (the interface would send these calls): *)
Lemma try_commute (a b c : nat) : a + (b + c) = a + (c + b).
Proof.
elpi point_run "Commute here" 11 14.
elpi point_run "Commute here (Elpi)" 11 14.
(* Try it: select the c + b on the right, click "Commute here".  A plain
   rewrite Nat.add_comm would swap the first sum, a + (b + c); the
   pattern makes it swap the selected one.
   → rewrite [X in _ = _ + X]Nat.add_comm. *)
(* Then click "Commute here (Elpi)": the same line.
   → rewrite [X in _ = _ + X]Nat.add_comm. *)
Abort.

(* A template is the right tool when the line is the same for every
   selection; write Elpi when the line depends on what is selected (3c).
   Everyday templates: *)
PointAction "Case on this" point "case E: ({text})."
  "case analysis on the selected term, with the equation E".
PointAction "Generalize this" point "move: ({text})."
  "generalize the selected term".
PointAction "Name this" point "{pre:in}set x := ({text}){post:in}."
  "name x the selected term (all its copies)".

Lemma try_case (n m : nat) : (n <=? m) = true \/ m < n.
Proof.
(* Try it: select n <=? m, click "Case on this".
   → case E: (n <=? m). *)
Abort.

Lemma try_generalize (a b : nat) : (a + b) * 2 = a + b + (a + b).
Proof.
(* Try it: select the first a + b, click "Generalize this".
   → move: (a + b). *)
(* Or click "Name this" (all the copies), or "Name occurrence" (this one).
   → set x := (a + b). *)
Abort.

(* ================ 5. How pbp is hooked ================

   pbp (pbp.v) knows nothing of selections.  Its API: pbp [X in C] takes
   a pattern of the goal that marks one subformula X, and does the
   logical steps that bring X to the surface; pbp [X Y in C] marks two
   and uses X to prove Y.  It acts on the goal only, so it needs the
   hypotheses moved to the goal first.

   It is hooked by two templates, with the path method pbp (2c) and the
   strategy revert (2d): *)
(* point_actions.v, lines 495-498:
PointAction "Point" point "{pre:revert}pbp {path:pbp}{post:revert}."
  "pbp: bring the selected subformula to the surface of the goal".
PointAction "Link" link "{pre:revert}pbp {path:pbp}{post:revert}."
  "pbp: link the two selected subformulas".
*)
(* revert writes what point-revert gives, before the core: *)
(* pbp_select.v, lines 512-515:
pred point-revert i:point-in, o:string.
point-revert (point-in _ [] _ _ _) "" :- !.
point-revert (point-in _ Hs _ _ _) M :-
  std.string.concat " " Hs HsS, M is "move: " ^ HsS ^ "; ".
*)
Lemma and_swap (A B : Prop) (H : A /\ B) : B /\ A.
Proof.
(* Try it: select the A of H, click "Point".  pbp splits H: the goal is
   then B /\ A with the two parts of H as hypotheses.
   → move: H; pbp [X in X /\ _ -> _]. *)
Abort.

(* Hooking your own tactic, the same way.  The tactic: zero_left [X in C]
   writes the number at the place X of the goal as 0 + it.  Like pbp, it
   takes a pattern ([X in C] is pbp.v's notation for fun X => C, the _
   being holes). *)
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

(* The action, as Point: the pattern in C, the hypotheses moved first. *)
PointAction "Zero left" point "{pre:revert}zero_left {path:pbp}{post:revert}."
  "write the selected number n as 0 + n".

Lemma try_zero (a b : nat) (H : a + b = b) : a = 0.
Proof.
(* Try it: select the a of the conclusion, click "Zero left".
   → zero_left [X in X = _]. *)
(* Or select the a of H, click "Zero left".
   → move: H; zero_left [X in X + _ = _ -> _]. *)
Abort.

(* To hook a tactic: give it an argument that a path method writes (a
   pattern, an occurrence, a path), or write the method (3a); choose how
   it treats hypotheses, a strategy (2d, 3b); declare the action, by a
   template or, when the line depends on the selection, in Elpi (3c).
   A template does not check that the line makes sense: Zero left on a
   selection that is not a number writes a line that fails when it is
   run. *)
