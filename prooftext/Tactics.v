(* prooftext: the bounded searches that the tools run for a tactic a proof
   text may name (tactics.elpi), so that the reader (cyp) and the writer
   (xtext) run the same one.  firstorder has no bound: on some goals it
   runs for minutes and gigabytes; for the name firstorder both tools run
   bounded_firstorder, a proof search of bounded depth, with no time limit
   (it fails after a bounded number of steps). *)

(* the number of steps of decompose_all on one goal: each step is an
   intro, a split or a hypothesis taken apart *)
Ltac decompose_steps := constr:(200%nat).

(* the goal unfolded and introduced, its conjunctions split, and the
   connectives of the hypotheses taken apart, at most n steps deep (n a
   nat).  Without the bound it may not end: split applies the constructor
   of any inductive type with one constructor, and on
     Inductive U : nat -> Prop := cu : forall n, U (S n) -> U n.
   the goal U 0 gives U 1, U 2, ... for ever *)
Ltac decompose_n n :=
  lazymatch n with
  | S ?m =>
      tryif once (intro || split || match goal with
        | H : _ /\ _ |- _ => destruct H
        | H : _ <-> _ |- _ => destruct H
        | H : _ \/ _ |- _ => destruct H
        | H : exists _, _ |- _ => destruct H
        | H : False |- _ => destruct H
        end)
      then decompose_n m else idtac
  | O => idtac
  end.
(* once: the first way only, as repeat does (no backtracking into the steps
   when the tactic after it fails) *)
Ltac decompose_all := let n := decompose_steps in once (decompose_n n).
(* the closing tactic: a proof search of depth 4 with the hypotheses, or
   equational reasoning *)
Ltac gap_close := solve [ eauto 4 | congruence ].

(* first-order reasoning, bounded: what cyp runs for firstorder; the
   second time after a simplification (a function on a constructor) *)
Ltac bounded_firstorder :=
  solve [ decompose_all; gap_close
        | decompose_all; simpl in *; decompose_all; gap_close ].

(* lia and nia have no bound in Rocq 9.1 (the options Lia Depth and Lra
   Depth are not read by the search).  lia_guard is a check of the goal's
   shape before them, with no search and no time: it counts, in the
   hypotheses that are propositions and in the goal, the occurrences of
   what makes lia split into cases (a disjunction, an equivalence, a
   negation, an implication inside a hypothesis; in the goal, which lia
   negates, a conjunction or an equality; a function defined by cases:
   sub, pred, max, min, abs, div, modulo, quot, rem, sgn, to_nat), and the
   hypotheses that are propositions; it fails, with a message, above 50
   case splits or 16 hypotheses (the two numbers of lia_guard below).
   They were measured (2026-11-23) on every call of lia and nia in the
   texts of xtext, cyp's runs on them and on cyp's examples, and the
   probe of xtext/gaps (xtext/gaps/README.md, "lia_guard"): the largest
   call that succeeded had 34 case splits and 8 hypotheses; each bound is
   about 1.5 and 2 times that.  The counts are an over-approximation of
   the splits lia makes (each occurrence counts, whatever its polarity).
   The guard bounds the size of what lia is given, not lia's search: a
   goal under the bounds may still be hard (nia on a nonlinear goal).
   None of the measured calls ran away.
   lia_stats prints the two counts (for measurements). *)
From Stdlib Require Import Lia.
From elpi Require Import elpi.
Elpi Tactic lia_guard.
Elpi Accumulate lp:{{
% the case splits lia (nia) may make on a sequent: a disjunction, an
% equivalence, a negation, an implication between hypotheses' parts; in
% the goal (negated by lia) a conjunction or an equality; and the
% functions defined by cases (sub, pred, max, min, abs, div, modulo, ...)
pred split-fun i:string.
split-fun S :- std.mem! ["or","iff","not","sub","pred","max","min","abs","div","modulo","quot","rem","sgn","to_nat","Zabs_nat","abs_nat"] S.
pred split-goal i:string.
split-goal S :- std.mem! ["and","eq"] S.
pred splits i:bool, i:term, o:int.
splits G (global GR) 1 :- coq.gref->id GR S, (split-fun S ; G = tt, split-goal S), !.
splits G (pglobal GR _) N :- !, splits G (global GR) N.
splits G (app L) N :- !, std.fold L 0 (t\a\b\ sigma M\ splits G t M, b is a + M) N.
splits G (prod _ A B) N :- !, splits G A NA,
  (pi x\ splits G (B x) NB),
  (if (G = ff, B = (_\ _)) (N is NA + NB + 1) (N is NA + NB)).
splits G (fun _ A B) N :- !, splits G A NA, (pi x\ splits G (B x) NB), N is NA + NB.
splits G (let _ A V B) N :- !, splits G A NA, splits G V NV, (pi x\ splits G (B x) NB), N is NA + NB + NV.
splits _ _ 0.
% the hypotheses that are propositions (lia's input)
pred prop-hyp i:prop.
prop-hyp (decl _ _ Ty) :- coq.typecheck Ty S ok, S = sort prop.
pred hyp-type i:prop, o:term.
hyp-type (decl _ _ Ty) Ty.
pred stats i:goal-ctx, i:term, o:int, o:int.
stats Ctx Ty N H :-
  std.filter Ctx prop-hyp Ps, std.length Ps H,
  std.map Ps hyp-type Ts,
  std.fold Ts 0 (t\a\b\ sigma M\ splits ff t M, b is a + M) N0,
  splits tt Ty NG, N is N0 + NG.
solve (goal Ctx _ Ty _ [int K, int M]) _ :- !,
  stats Ctx Ty N H,
  if (N > K) (coq.ltac.fail 0 "lia_guard:" N "case splits, at most" K) true,
  if (H > M) (coq.ltac.fail 0 "lia_guard:" H "hypotheses, at most" M) true.
solve (goal Ctx _ Ty _ [str "stats"]) _ :- !,
  stats Ctx Ty N H, coq.say "LIA_STATS splits" N "hyps" H.
% the same, the line starting with a prefix (a tool may show only some lines)
solve (goal Ctx _ Ty _ [str "stats", str P]) _ :- !,
  stats Ctx Ty N H, coq.say P "LIA_STATS splits" N "hyps" H.
}}.
Ltac lia_guard := elpi lia_guard 50 16.
Ltac lia_stats := elpi lia_guard "stats".
(* lia and nia behind the guard *)
Ltac guarded_lia := lia_guard; lia.
Ltac guarded_nia := lia_guard; nia.
