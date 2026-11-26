(* Tests of subterm_select.v.

   1. The examples of the paper (Gonthier and Tassi, ITP 2012): 1, 2
      (fragility), 5, 6, 7, 8, 9, in a small ring-like setting where, as in
      the paper, a - b is a + - b; the selected positions are checked
      (pattern_select_expect), and the later instances
      (pattern_select_later_expect); select_all on the same positions, its
      best candidate against the paper's pattern (select_all_vs).
   2. The algebra: law 3 of GRAMMAR.md on f a 1 + f b (g 2) = 0.
   3. The round trip of the paths on the goals of point_paths_test.v: for
      every path p of the conclusion and of the hypotheses, point_to_pattern
      gives a pattern [X in C] (for the path p, or the one it is widened
      to); pattern_select on that pattern must give exactly that path; and
      the kind of select_all's best candidate for every path. *)

From Stdlib Require Import String.
From elpi Require Import elpi.
From coq_tmp Require Import subterm_select point_actions point_actions_more.

(* ---------------- 1. The examples of the paper ---------------- *)

Module Paper.
Section Ring.
Variables (R : Type) (zero two : R) (add mul : R -> R -> R) (opp : R -> R).
Declare Scope ring_scope.
Delimit Scope ring_scope with ring.
Local Notation "0" := zero : ring_scope.
Local Notation "2" := two : ring_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "x - y" := (add x (opp y)) : ring_scope.
Local Open Scope ring_scope.

(* Ex. 1: [_ - a] has one instance, b * c - a *)
Goal forall a b c : R, a + (b * c - a) + a = b * c + a.
intros a b c.
elpi pattern_select "[_ - a]".
elpi pattern_select_expect "[_ - a]" "2.1.2".
elpi select_all "2.1.2".
elpi select_all_vs "2.1.2" "[_ - a]".
elpi select_all_expect "2.1.2" "_ - a".
(* Ex. 2 (fragility): the instantiation by name, b * c + _, selects
   b * c - a too here (it is b * c + - a), but it has a later instance,
   b * c + a: what it selects when the goal changes (below) *)
elpi pattern_select_expect "[b * c + _]" "2.1.2".
elpi pattern_select_later_expect "[b * c + _]" "3".
Abort.

(* Ex. 2: the goal changed: [_ - a] fails, [b * c + _] selects its later
   instance (both occurrences of b * c + a) *)
Goal forall a b c : R, a + (b * c + a) + a = b * c + a.
intros a b c.
elpi pattern_select_fails "[_ - a]".
elpi pattern_select "[b * c + _]".
elpi pattern_select_expect "[b * c + _]" "2.1.2 3".
Abort.

(* Ex. 5: all the occurrences of the first instance, a - b; the later
   instance d - b *)
Goal forall a b c d : R, (a - b) + (b - c) = (a - b) + (d - b).
intros a b c d.
elpi pattern_select "[_ - b]".
elpi pattern_select_expect "[_ - b]" "2.1 3.1".
elpi pattern_select_later_expect "[_ - b]" "3.2".
(* select_all: a - b occurs twice, so a single one needs an occurrence
   switch or a context; d - b alone is univocal *)
elpi select_all "2.1".
elpi select_all "3.2".
elpi select_all_expect "3.2" "d + _".
(* an occurrence switch: the second occurrence of the first instance *)
elpi pattern_select_expect "{2}[_ - b]" "3.1".
Abort.

(* Ex. 6: the X part of snd (_, X); snd and pair have their two type
   arguments as implicit arguments (paths 1 and 2) *)
Goal forall a b c : R, 0 = snd (0 * c, 0 * (a + b)).
intros a b c.
elpi pattern_select "[X in snd (_, X)]".
elpi pattern_select_expect "[X in snd (_, X)]" "3.3.4".
elpi select_all "3.3.4".
elpi select_all_vs "3.3.4" "[X in snd (_, X)]".
(* without a context: 0 * c first *)
elpi pattern_select_expect "[0 * _]" "3.3.3".
Abort.

(* Ex. 7: _ + b in the right-hand side only *)
Variable f : R -> R.
Goal forall a b c : R, a + b = f (a * a + b) - c.
intros a b c.
elpi pattern_select "(_ + b in X in _ = X)".
elpi pattern_select_expect "(_ + b in X in _ = X)" "3.1.1".
elpi select_all "3.1.1".
elpi select_all_vs "3.1.1" "(_ + b in X in _ = X)".
elpi pattern_select_expect "(_ + b)" "2".
(* the named context RHS of ssrmatching *)
elpi pattern_select_expect "(_ + b in RHS)" "3.1.1".
Abort.

(* Ex. 8: the third form, _ + d as X in f2 _ X: the second f2 *)
Variable f2 : R -> R -> R.
Goal forall a b c d : R, f2 (a + b) (2 * (a + c)) + (c + d) + f2 a (c + d) = 0.
intros a b c d.
elpi pattern_select "[_ + d as X in f2 _ X]".
elpi pattern_select_expect "[_ + d as X in f2 _ X]" "2.2.2".
elpi select_all "2.2.2".
elpi select_all_vs "2.2.2" "[_ + d as X in f2 _ X]".
elpi pattern_select_expect "[X in f2 _ X]" "2.1.1.2".
(* the rewrite-only patterns are not c-patterns: set refuses them *)
elpi pattern_select_fails "[in f2 _ _]".
elpi pattern_select_fails "[in X in f2 _ X]".
Abort.

(* Ex. 9: (_ + _) in X in (_ * X): the a + b inside the X part only *)
Goal forall a b d : R, a + b + (a * ((a + b) * d)) = 0.
intros a b d.
elpi pattern_select "((_ + _) in X in (_ * X))".
elpi pattern_select_expect "((_ + _) in X in (_ * X))" "2.2.2.1".
elpi select_all "2.2.2.1".
elpi select_all_vs "2.2.2.1" "((_ + _) in X in (_ * X))".
elpi pattern_select_expect "(_ + _)" "2".
Abort.
End Ring.
End Paper.

(* the hypothesis variant, a prefix of an application, an implicit
   argument, a pattern under a binder *)
Goal forall (f : nat -> nat -> nat) a b, f a b + f b a = 0 -> forall n, n + 0 = f a n.
intros f a b H.
elpi pattern_select "H" "[f _ a]".
elpi pattern_select_expect "H" "[f _ a]" "2.2".
elpi pattern_select_expect "H" "[X in _ = X]" "3".
(* f a is a prefix of f a b: written 2.1<1 (the application at 2.1
   without its last argument) *)
elpi pattern_select_expect "H" "[f a]" "2.1<1".
(* nat, the implicit type of eq: path 1, not printed *)
elpi pattern_select "H" "[nat]".
elpi pattern_select_expect "H" "[nat]" "1".
(* under the binder n: n + 0 uses n, set cannot select it *)
elpi pattern_select_fails "[_ + 0]".
elpi pattern_select_fails "[f a _]".
Abort.

(* ---------------- 2. The algebra (GRAMMAR.md, law 3) ---------------- *)

(* [elpi selector_expect N Exp]: the selector number N below denotes the
   positions Exp in the conclusion ("error" when it fails) *)
Elpi Tactic selector_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
pred selector i:int, o:selector.
% ⟨f _ X | X⟩ ; ⟨g Y | Y⟩
selector 1 (s-then (s-hole "f _ X" "X") (s-hole "g Y" "Y")).
% ⟨f _ (g Y) | Y⟩
selector 2 (s-hole "f _ (g Y)" "Y").
% 2 ; 1 ; ⟨g _⟩: a path, then a match
selector 3 (s-then (s-then (s-step 2) (s-step 2)) (s-match "g _")).
% ⟨f _ _⟩ # {2}  and  ⟨f _ _⟩ ∪ ⟨g _⟩
selector 4 (s-pick (s-match "f _ _") (pick-in [2])).
selector 5 (s-union (s-match "f _ _") (s-match "g _")).
solve (goal _ _ Ty _ [int N, str Exp] as G) [seal G] :-
  selector N S, sel-denote G "" Ty [] S R, sel-show S SS,
  (R = sel-ok Qs, !, sel-positions-string Qs Got ; Got = "error"),
  coq.say SS "denotes" Got,
  (Got = Exp, ! ; coq.ltac.fail 0 "selector_expect:" SS "got" Got "expected" Exp).
}}.

Goal forall (f : nat -> nat -> nat) (g : nat -> nat) (a b : nat), f a 1 + f b (g 2) = 0.
intros f g a b.
(* law 3: the first f _ _ is f a 1, whose X part has no g: the left one
   fails; the flattened one takes the second f *)
elpi selector_expect 1 "error".
elpi selector_expect 2 "2.2.2.1".
elpi selector_expect 3 "2.2.2".
(* the pick is the oracle's {2}: f a 1 has one occurrence, and set refuses
   an occurrence number beyond the occurrences: an error *)
elpi selector_expect 4 "error".
elpi selector_expect 5 "2.1 2.2.2".
Abort.

(* ---------------- 3. The round trip of the paths ---------------- *)

(* [elpi select_roundtrip Exp]: for every path p of the conclusion and of
   each hypothesis, the pattern of point_to_pattern (for p, or the path it
   is widened to, q) must select exactly q.  It prints the counts: the
   paths tried, univocal (exactly {q}), multiple (q and other occurrences:
   the pattern is right but selects more), mismatch (q not selected),
   refused (ssreflect refuses the pattern), no pattern (point_to_pattern
   gives none: a path through a binder name); then each case that is not
   univocal.  It fails unless the counts are Exp, "paths univocal multiple
   mismatch refused nopattern". *)
Elpi Tactic select_roundtrip.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{

kind rt type.
type rt-ok, rt-multiple, rt-mismatch, rt-refused, rt-nopattern rt.

% [rt-one Ctx G H P Out Line] Out is the outcome of the round trip of the
% path P of the part H of G, Line its description
pred rt-one i:goal-ctx, i:goal, i:string, i:list int, o:rt, o:string.
rt-one Ctx (goal _ _ Ty _ _ as G) H P Out Line :-
  sel-pos-string (sp-at P) PS,
  (H = "", !, Sels = [sel-goal P], Where = PS ; Sels = [sel-hyp H P], Where is H ^ " " ^ PS),
  (point-resolve Ctx Ty Sels In _, In = point-in _ _ _ _ [loc _ _ Q],
   point-local-pattern In Pat, !,
   sel-pos-string (sp-at Q) QS,
   sel-select G H Pat _ R,
   (R = sel-error M, !, Out = rt-refused, Line is Where ^ ": " ^ Pat ^ " refused: " ^ M ;
    R = sel-ok Qs, sel-positions-string Qs Got, sel-pos-string (sp-at Q) QS1,
    (Qs = [sp-at Q], !, Out = rt-ok, Line = "" ;
     std.mem Qs (sp-at Q), !, Out = rt-multiple,
     Line is Where ^ " (selection " ^ QS ^ "): " ^ Pat ^ " selects " ^ Got ;
     Out = rt-mismatch,
     Line is Where ^ " (selection " ^ QS1 ^ "): " ^ Pat ^ " selects " ^ Got)) ;
   Out = rt-nopattern, Line is Where ^ ": no pattern").

% [rt-part Ctx G H T Rs] Rs are the outcomes for the paths of T, the part H
pred rt-part i:goal-ctx, i:goal, i:string, i:term, o:list (pair rt string).
rt-part Ctx G H T Rs :-
  std.findall (path-of T P_) Sols, std.map Sols (s\ p\ s = path-of _ p) Ps,
  std.map Ps (p\ r\ sigma O L\ rt-one Ctx G H p O L, r = pr O L) Rs.

pred rt-count i:list (pair rt string), i:rt, o:int.
rt-count Rs O N :- std.filter Rs (r\ r = pr O _) L, std.length L N.

solve (goal Ctx _ Ty _ [str Exp] as G) [seal G] :-
  tool-name "select_roundtrip" => (
  rt-part Ctx G "" Ty R0,
  std.map-filter Ctx (e\ h\ sigma V N T S\ e = decl V N T,
     coq.typecheck T S ok, S = sort prop, coq.name->id N h) Hs,
  std.map Hs (h\ r\ sigma T\ sel-part G h T, rt-part Ctx G h T r) RHs,
  std.flatten [R0|RHs] Rs,
  std.length Rs NP,
  std.map [rt-ok, rt-multiple, rt-mismatch, rt-refused, rt-nopattern] (rt-count Rs) Ns,
  std.map [NP|Ns] (n\ s\ s is int_to_string n) NSs, std.string.concat " " NSs Got,
  std.map-filter Rs (r\ l\ r = pr _ l, not (l = "")) Ls,
  std.string.concat "\n  " Ls LS,
  coq.say "round trip: paths univocal multiple mismatch refused nopattern =" Got "\n " LS,
  (Exp = "?", ! ; Got = Exp, ! ; coq.ltac.fail 0 "select_roundtrip: got" Got "expected" Exp)).
% (Exp = "?": print only)
}}.

Definition double n := n + n.

(* [elpi select_all_causes]: for every path whose best candidate needs an
   occurrence number or is the path alone, prints a line
   "CAUSE <class> <cause> <where> <path> : <text>", the cause being the
   first that applies: root, binder-name, hidden (not printed), head,
   bound (uses a variable bound in the goal), cast, under-binder (closed,
   but below a binder of the goal), copy (another subterm is the same
   term), other. *)
Elpi Tactic select_all_causes.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
pred sc-cause i:term, i:list int, o:string.
sc-cause _ [] "root" :- !.
sc-cause T P "binder-name" :- name-at T P _, !.
sc-cause T P "hidden" :- sel-hidden T P, !.
sc-cause _ P "head" :- P = [_|_], std.last P L, L = 0, !.
sc-cause T P "bound" :- not (term-at P T _), !.
sc-cause T P "cast" :- sel-cast-at P T, !.
sc-cause T P "under-binder" :- through-binder T P, !.
sc-cause T P "copy" :- term-at P T Tt, sel-closed [] T [] [] Ps,
  std.exists Ps (q\ not (q = P), term-at q T C, same_term C Tt), !.
sc-cause _ _ "other".

% [through-binder T P] the path P goes below a binder of T
pred through-binder i:term, i:list int.
through-binder T [I|P] :- kid-at T I (k\ (k = kb _ _ _ ; k = kt U, through-binder U P)).

pred sc-part i:goal, i:string, i:term.
sc-part G H T :-
  std.findall (path-of T P_) Sols, std.map Sols (s\ p\ s = path-of _ p) Ps,
  std.forall Ps (p\ sigma Rs K C Cause PS Txt\
    sg-select-all G H p Rs, sg-best Rs (sg-res _ K _ _ _),
    (std.mem! [e1-occurrence-switch, a2-occurrence] K, !, C = "occurrence" ;
     K = a1-path, !, C = "path" ; C = ""),
    (C = "", ! ;
     sc-cause T p Cause, sel-pos-string (sp-at p) PS, sel-pos-text T (sp-at p) Txt,
     coq.say "CAUSE" C Cause H PS ":" Txt)).

solve (goal Ctx _ Ty _ [] as G) [seal G] :-
  tool-name "select_all_causes" => (
  sc-part G "" Ty,
  std.map-filter Ctx (e\ h\ sigma V N T S\ e = decl V N T,
     coq.typecheck T S ok, S = sort prop, coq.name->id N h) Hs,
  std.forall Hs (h\ sigma T\ sel-part G h T, sc-part G h T)).
}}.

(* [elpi select_all_roundtrip Exp]: for every path p of the conclusion
   and of each hypothesis (a proposition), select_all's best candidate
   (checked by the oracle: it denotes exactly {p}) is counted by kind:
   "paths B C occurrence path", B a term pattern, C a context (C1, C2,
   C3), occurrence an occurrence number (E1, A2), path: no ssreflect form,
   the path only.  It prints the counts and fails unless they are Exp
   ("?": print only). *)
Elpi Tactic select_all_roundtrip.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
pred sa-class i:sel-kind, o:int.
sa-class K 0 :- std.mem! [b1-closed-term, b2-term-with-holes, b3-flexible-head, b4-type-driven] K, !.
sa-class K 1 :- std.mem! [c1-context, c2-redex-in-context, c3-redex-as-context] K, !.
sa-class K 2 :- std.mem! [e1-occurrence-switch, a2-occurrence] K, !.
sa-class _ 3.

pred sa-part i:goal, i:string, i:term, o:list int.
sa-part G H T Cls :-
  std.findall (path-of T P_) Sols, std.map Sols (s\ p\ s = path-of _ p) Ps,
  std.map Ps (p\ c\ sigma Rs K\ sg-select-all G H p Rs, sg-best Rs (sg-res _ K _ _ _), sa-class K c) Cls.

solve (goal Ctx _ Ty _ [str Exp] as G) [seal G] :-
  tool-name "select_all_roundtrip" => (
  sa-part G "" Ty C0,
  std.map-filter Ctx (e\ h\ sigma V N T S\ e = decl V N T,
     coq.typecheck T S ok, S = sort prop, coq.name->id N h) Hs,
  std.map Hs (h\ c\ sigma T\ sel-part G h T, sa-part G h T c) CHs,
  std.flatten [C0|CHs] Cs, std.length Cs N,
  std.map [0, 1, 2, 3] (k\ n\ sigma L\ std.filter Cs (c\ c = k) L, std.length L n) Ns,
  std.map [N|Ns] (n\ s\ s is int_to_string n) NSs, std.string.concat " " NSs Got,
  coq.say "select_all round trip: paths B C occurrence path =" Got,
  (Exp = "?", ! ; Got = Exp, ! ; coq.ltac.fail 0 "select_all_roundtrip: got" Got "expected" Exp)).
}}.

(* The select_all round trip on the same goals: of the 531 paths, the best
   candidate (each one checked by the oracle to denote exactly the path)
   is a term pattern for 142, a context for 135, needs an occurrence
   number for 142, and is the path alone (no ssreflect form) for 112. *)
(* The goals of point_paths_test.v, in its order.  In all: 531 paths, 387
   univocal, 0 multiple, 15 mismatches, 129 refused, 0 without pattern.
   What the cases that are not univocal say about the translation path ->
   [X in C] of subterm_pattern.v (ssreflect being the judge):
   - refused, [X in X] (75): the whole part, and every path widened to it
     (the paths inside an implicit argument, the return type of a match):
     set refuses X in X ("indeterminate pattern");
   - refused, X applied to holes (45): the head of an application, X _ _
     (or X _ _ _ for a head with three arguments): "partial term ... does
     not match" (42), or "The pattern _ did not match" in a branch (3);
   - refused, anomalies of set (9): patterns with X under a fun of the
     pattern ([x0 : nat in X x0 + _], [k : X in _]): "Evar not declared"
     (5, caught by run_tactic_string) or "Uncaught exception Not_found"
     (4, reported by set as an error);
   - mismatches (15), 13 of them from X applied to the variables bound above it
     (X a b, [x : nat in X x], exists y, X c y) is matched up to eta, and
     the goal that set gives does not tell apart the readings: X a b
     against a + b gives X := Nat.add, z a b in the goal, the head (we
     read 2.2.2.2.0, not 2.2.2.2); X u v against u = v gives the prefix
     @eq nat; exists y, X c y gives fun y => z c y, the fun or its body
     (we read the body); plus the cast goal, where set erases the cast
     (n : nat) and [X in (X : nat) = _] reads as the cast (flagged), and
     the head of the root of the string goal, X _ _ _, which matches the
     Ascii applications inside the strings. *)
Goal forall a : nat, 1 + 1 + a = double (1 + a).
intros a.
elpi select_roundtrip "22 19 0 0 3 0".
elpi select_all_roundtrip "22 6 10 6 0".
Abort.

Goal forall a b : nat, a = b -> b = a.
intros a b ab.
elpi select_roundtrip "10 4 0 0 6 0".
elpi select_all_roundtrip "10 10 0 0 0".
Abort.

Goal ("a b" = "a b")%string.
elpi select_roundtrip "77 74 0 0 3 0".
elpi select_all_roundtrip "77 3 62 12 0".
Abort.

Goal forall (p : nat * nat), (let '(a, b) := p in a + b) = 0 -> True.
intros p H.
elpi select_roundtrip "21 13 0 4 4 0".
elpi select_all_roundtrip "21 8 3 4 6".
Abort.

Goal forall (n : nat) (b : bool), match n with 0 => true | S k => Nat.eqb k n end = (if b then false else true).
intros n b.
elpi select_roundtrip "22 17 0 2 3 0".
elpi select_all_roundtrip "22 5 2 10 5".
Abort.

Goal forall (b : bool), match b as x return (if x then nat else bool) with true => 0 | false => true end = match b as x return (if x then nat else bool) with true => 0 | false => true end.
intros b.
elpi select_roundtrip "35 26 0 0 9 0".
elpi select_all_roundtrip "35 3 2 21 9".
Abort.

Goal forall x : nat, (forall x : nat, x = x) -> forall y, (fun x => x + y) x = x.
intros x H.
elpi select_roundtrip "21 2 0 6 13 0".
elpi select_all_roundtrip "21 5 0 7 9".
Abort.

Goal forall (a b : nat) (c d : bool), (fun x y : nat => x + y) a b = a + b /\ exists (u v : nat) (w : bool), u = v /\ w = c.
elpi select_roundtrip "55 5 0 35 15 0".
elpi select_all_roundtrip "55 1 0 25 29".
Abort.

Goal forall n : nat, (n : nat) = n.
intros n.
change ((n : nat) = n).
elpi select_roundtrip "8 5 0 0 3 0".
elpi select_all_roundtrip "8 3 2 1 2".
Abort.

Module C.
From Stdlib Require Import ZArith.
Coercion Z.of_nat : nat >-> Z.
Record box := Box { unbox :> nat }.
Goal forall (n : nat) (b : box), (n + 1 = b)%Z /\ b + 0 = n.
intros n b.
elpi select_roundtrip "28 22 0 2 4 0".
elpi select_all_roundtrip "28 13 7 8 0".
Abort.
End C.

Set Printing All.
Goal forall a b : nat, a + b = b + a /\ (a <= b \/ True).
intros a b.
elpi select_roundtrip "20 15 0 0 5 0".
elpi select_all_roundtrip "20 11 7 2 0".
Abort.
Unset Printing All.

Goal forall n : nat, n = n.
intros n.
elpi select_roundtrip "5 2 0 0 3 0".
elpi select_all_roundtrip "5 3 2 0 0".
Abort.

Module IfMatch.
Notation "'IF' c 'THEN' a 'ELSE' b" := (if c then a else b) (at level 200).
Goal forall (b : bool) (n : nat), (IF b THEN n ELSE 0) = n.
intros b n.
elpi select_roundtrip "11 8 0 0 3 0".
elpi select_all_roundtrip "11 5 2 3 1".
Abort.
End IfMatch.

Goal forall (b : bool) (n : nat), (if b then n else 0) = n.
intros b n.
elpi select_roundtrip "11 8 0 0 3 0".
elpi select_all_roundtrip "11 5 2 3 1".
Abort.

Goal forall n : nat, match n with 0 => true | S _ => false end = true.
intros n.
elpi select_roundtrip "13 10 0 0 3 0".
elpi select_all_roundtrip "13 4 2 5 2".
Abort.

Goal forall n : nat, n + 0 = n.
elpi select_roundtrip "10 2 0 5 3 0".
elpi select_all_roundtrip "10 4 0 2 4".
Abort.

Goal forall n : nat, (let m := n + 1 in m * m) = n /\ (fun k : nat => k) n = n.
intros n.
elpi select_roundtrip "27 18 0 2 7 0".
elpi select_all_roundtrip "27 9 7 6 5".
Abort.

Goal forall (n : nat), match n with 0 => true | S k => Nat.eqb k n end = true -> (forall z : nat, z = z) -> True.
intros n H H'.
elpi select_roundtrip "24 11 0 6 7 0".
elpi select_all_roundtrip "24 6 2 9 7".
Abort.

Lemma two_is : 2 = 1 + 1. Proof. reflexivity. Qed.
Goal forall a : nat, double (1 + a) = 2 + a + a -> forall n : nat, n + double a = a.
intros a H.
elpi select_roundtrip "34 24 0 4 6 0".
elpi select_all_roundtrip "34 13 9 9 3".
Abort.

Goal forall a : nat, (if true then a else 0) = double 2.
intros a.
elpi select_roundtrip "17 13 0 0 4 0".
elpi select_all_roundtrip "17 9 2 5 1".
Abort.

Goal two_is = two_is.
elpi select_roundtrip "20 2 0 0 18 0".
elpi select_all_roundtrip "20 6 8 6 0".
Abort.

Goal forall a b : nat, a + b * 2 = b /\ forall n : nat, n * n = 0.
intros a b.
elpi select_roundtrip "27 18 0 5 4 0".
elpi select_all_roundtrip "27 9 4 10 4".
Abort.

Goal (exists m : nat, m = 0) /\ True.
elpi select_roundtrip "13 5 0 4 4 0".
elpi select_all_roundtrip "13 6 1 3 3".
Abort.
