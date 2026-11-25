(* The round trip of subterm_pattern.v: for every printed subterm of a
   goal (of its conclusion and of the types of its hypotheses), the
   pattern of its path, read back, designates it.

   [elpi pattern_roundtrip] takes each path P of a printed subterm (not
   the return type of a match nor a binder of a branch, nor inside
   them), computes its pattern [X in C] (path-pattern), parses and
   elaborates it again, and looks for X in the body C: X (or X applied
   to bound variables, or X with its type, (X : T)) must be at one place
   only, and that place must be P, or the path P' that path-pattern
   widened P to; the body must unify with the goal once X is the
   subterm at that place (check-ok).  It prints the number of paths, of
   those whose pattern designates the subterm itself, of those that
   designate a subterm above it printed with the same text (no warning:
   a coercion that is not printed), of those widened (with a warning),
   and of the mismatches, and fails if there is a mismatch.  The goals
   are the ones of point_paths_test.v. *)

From Stdlib Require Import ssreflect String.
From elpi Require Import elpi.
From coq_tmp Require Import subterm_pattern.

Elpi Tactic pattern_roundtrip.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate lp:{{

kind rt type.
% [rt Paths Exact Same Widened Bad] the counts of the round trip
type rt int -> int -> int -> int -> int -> rt.

% [rt-add A B C] C is the sum of the counts A and B
pred rt-add i:rt, i:rt, o:rt.
rt-add (rt A1 B1 C1 D1 E1) (rt A2 B2 C2 D2 E2) (rt A B C D E) :-
  A is A1 + A2, B is B1 + B2, C is C1 + C2, D is D1 + D2, E is E1 + E2.

% [places-of X T P Ps] Ps are the paths (reversed, below the reversed path
% P) where the variable X is in T: X, or X applied to variables (the bound
% variables the selection uses); the holes of T (unknowns of the
% elaboration) are left alone
pred places-of i:term, i:term, i:list int, o:list (list int).
places-of _ T _ [] :- var T, !.
places-of X T P [P] :- T == X, !.
places-of X (app [H|As]) P [P] :- H == X, std.forall As name, !.
places-of X T P Ps :- kids T Ks, std.length Ks N, std.iota N Is,
  std.map2 Is Ks (i\ k\ ps\ kid-places X k [i|P] ps) Pss, std.flatten Pss Ps.

pred kid-places i:term, i:kid, i:list int, o:list (list int).
kid-places _ (kn _) _ [].
kid-places X (kt T) P Ps :- places-of X T P Ps.
kid-places X (kb _ _ F) P Ps :- pi x\ places-of X (F x) P Ps.

% [place-of-x Pat P] the variable of the pattern Pat, parsed and
% elaborated, is at the path P of its body, and only there
pred place-of-x i:string, o:list int.
place-of-x Pat P :-
  S is "(" ^ Pat ^ ")", coq.parse.argument S ff "" (trm (fun N Ty F)) ok,
  pi x\ decl x N Ty => (places-of x (F x) [] [R], std.rev R P).

% [rt-path Ctx M T P R] R counts the round trip of the path P of T
pred rt-path i:list string, i:bmode, i:term, i:list int, o:rt.
rt-path Ctx M T P R :-
  path-pattern Ctx M T P P1 Pat W, !,
  % (X applied to variables is also the head of an application of the
  % selection to these variables: then the selection is at Q.0; a
  % selected fun may be printed eta-expanded, fun y => X y, as the fun
  % of exists y, ..: then X is in its body, at P1.2; X written with its
  % type, (X : T), is the term of a cast, at P1.1)
  (check-ok Pat [P1] T,
   not (not (place-of-x Pat Q,
             (Q = P1 ; std.append Q [0] P1 ; std.append P1 [2] Q ;
              std.append P1 [1] Q))), !,
   (P1 = P, !, R = rt 1 1 0 0 0 ; W = "", !, R = rt 1 0 1 0 0 ; R = rt 1 0 0 1 0) ;
   string-of-path P PS, coq.say "MISMATCH" PS Pat, R = rt 1 0 0 0 1).
rt-path _ _ _ P (rt 1 0 0 0 1) :- string-of-path P PS, coq.say "NO PATTERN" PS.

% [rt-term Ctx M T R] R counts the round trip of the printed paths of T
pred rt-term i:list string, i:bmode, i:term, o:rt.
rt-term Ctx M T R :-
  std.findall (path-of T P_) Sols,
  std.map-filter Sols (s\ p\ s = path-of T p, printed-at T p) Ps,
  std.map Ps (rt-path Ctx M T) Rs, std.fold Rs (rt 0 0 0 0 0) rt-add R.

solve (goal Ctx _ Ty _ [] as G) [seal G] :-
  std.map-filter Ctx (d\ h\ sigma V N T B\ (d = decl V N T ; d = def V N T B),
                         coq.name->id N h) Names,
  rt-term Names (bm-goal 0) Ty R0,
  std.map-filter Ctx (d\ t\ sigma V N\ d = decl V N t) Hyps,
  std.map Hyps (rt-term Names bm-hyp) Rs, std.fold Rs R0 rt-add R,
  R = rt N Ex Sa Wi Bad,
  coq.say "roundtrip: paths" N "exact" Ex "same-text" Sa "widened" Wi "mismatches" Bad,
  (Bad = 0, ! ; coq.ltac.fail 0 "pattern_roundtrip: mismatches").
}}.
Definition double n := n + n.

Goal forall a : nat, 1 + 1 + a = double (1 + a).
intros a. elpi pattern_roundtrip.
Abort.

Goal forall a b : nat, a = b -> b = a.
intros a b ab. elpi pattern_roundtrip.
Abort.

Goal ("a b" = "a b")%string.
elpi pattern_roundtrip.
Abort.

Goal forall (p : nat * nat), (let '(a, b) := p in a + b) = 0 -> True.
intros p H. elpi pattern_roundtrip.
Abort.

Goal forall (n : nat) (b : bool), match n with 0 => true | S k => Nat.eqb k n end = (if b then false else true).
intros n b. elpi pattern_roundtrip.
Abort.

Goal forall (b : bool), match b as x return (if x then nat else bool) with true => 0 | false => true end = match b as x return (if x then nat else bool) with true => 0 | false => true end.
intros b. elpi pattern_roundtrip.
Abort.

Goal forall x : nat, (forall x : nat, x = x) -> forall y, (fun x => x + y) x = x.
intros x H. elpi pattern_roundtrip.
Abort.

Goal forall (a b : nat) (c d : bool), (fun x y : nat => x + y) a b = a + b /\ exists (u v : nat) (w : bool), u = v /\ w = c.
elpi pattern_roundtrip.
Abort.

Goal forall n : nat, (n : nat) = n.
intros n. elpi pattern_roundtrip.
Abort.

Module C.
From Stdlib Require Import ZArith.
Coercion Z.of_nat : nat >-> Z.
Record box := Box { unbox :> nat }.
Goal forall (n : nat) (b : box), (n + 1 = b)%Z /\ b + 0 = n.
intros n b. elpi pattern_roundtrip.
Abort.
End C.

Set Printing All.
Goal forall a b : nat, a + b = b + a /\ (a <= b \/ True).
intros a b. elpi pattern_roundtrip.
Abort.
Unset Printing All.

Module IfMatch.
Notation "'IF' c 'THEN' a 'ELSE' b" := (if c then a else b) (at level 200).
Goal forall (b : bool) (n : nat), (IF b THEN n ELSE 0) = n.
intros b n. elpi pattern_roundtrip.
Abort.
End IfMatch.

Goal forall n : nat, match n with 0 => true | S _ => false end = true.
intros n. elpi pattern_roundtrip.
Abort.

Goal forall n : nat, (let m := n + 1 in m * m) = n /\ (fun k : nat => k) n = n.
intros n. elpi pattern_roundtrip.
Abort.

Goal forall (n : nat), match n with 0 => true | S k => Nat.eqb k n end = true -> (forall z : nat, z = z) -> True.
intros n H H'. elpi pattern_roundtrip.
Abort.

Goal forall a : nat, double (1 + a) = 2 + a + a -> forall n : nat, n + double a = a.
intros a H. elpi pattern_roundtrip.
Abort.

Goal (exists m : nat, m = 0) /\ True.
elpi pattern_roundtrip.
Abort.
