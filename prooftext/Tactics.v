(* prooftext: the tactics that the words of a proof text mean (word_N,
   at the end), and the bounded searches that the tools run for a tactic a proof
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
   shape before them, with no search and no time: it counts the cases that
   lia would refute, the way lia makes them, and the hypotheses it reads,
   and fails, with a message, above 2^18 cases (18 case splits) or 16
   hypotheses (the two numbers of lia_guard below).

   What lia does (Stdlib's micromega/Lia.v: lia is Zify.zify; xlia):
   - zify starts with intros (micromega/Zify.v): the products in front of
     the goal become hypotheses, a dependent one (forall k : Z, ...) a
     variable; nothing else is unfolded (~ A stays the goal).
   - zify adds, for each distinct application of Z.abs, Z.max, Z.min,
     Z.sgn (and of what it turns into them: the truncated sub and pred
     of nat, N and positive, Z.to_nat, Z.abs_nat, ...), a hypothesis with
     two cases (three for Z.sgn) (micromega/ZifyInst.v, the UnOpSpec and
     BinOpSpec; one per distinct term: plugins/micromega/zify.ml,
     spec_of_term), wherever the term is, but not under a binder; with
     the division flag, each distinct div or mod (Z.div_mod_to_equations)
     gives a hypothesis with cases too: counted two, with or without the
     flag (an upper bound).
   - xlia reads each hypothesis that is a proposition and the goal as a
     formula (plugins/micromega/coq_micromega.ml, parse_formula): /\, \/,
     <->, ~, True, False and an implication A -> B (a product whose
     variable does not occur) are connectives; a comparison of integers
     (<=, <, >=, >, = on Z, nat, N, positive; = on bool) is an atom;
     anything else (a forall, a comparison on R, a predicate) is an atom
     lia knows nothing of.
   - the formula hypotheses -> goal is put in clausal form
     (micromega/Tauto.v, xcnf; ZMicromega.v, normalise and negate), and
     lia refutes each clause on its own: the number of clauses is the
     number of cases.  An unknown atom contributes nothing: its form is
     cnf_ff, which or_cnf_opt drops and which absorbs and_cnf_opt (a
     hypothesis A \/ P, P unknown, is not used; A /\ P is used as A); an
     equality in the goal (a disequality in a hypothesis) is two cases
     (x < y, x > y); a disjunction or implication of hypotheses, a
     conjunction of the goal, multiplies the cases of its two sides.
   lia_guard computes this number with the same rules (it does not drop a
   clause that is trivially true, as lia may: an upper bound) and counts
   its case splits, log2 of the cases rounded up; the hypotheses are the
   ones whose form is not dropped.
   The bounds were measured (2026-11-24) on every call of lia and nia in
   the texts of xtext, cyp's runs on them and on cyp's examples, and the
   probe of xtext/gaps (xtext/gaps/README.md, "lia_guard"): the largest
   call that succeeded had 12 case splits and 8 hypotheses; each bound is
   1.5 and 2 times that.  The guard bounds the size of what lia is given,
   not lia's search: a goal under the bounds may still be hard (nia on a
   nonlinear goal).  None of the measured calls ran away.
   lia_stats prints the counts (for measurements). *)
From Stdlib Require Import Lia.
From Stdlib Require BinInt BinNat BinPos PeanoNat.
From elpi Require Import elpi.
Elpi Tactic lia_guard.
Elpi Accumulate lp:{{
% The size of a clausal form (micromega/Tauto.v): -1 for cnf_ff (an
% unknown atom: dropped by a disjunction, absorbs a conjunction), 0 for
% cnf_tt (true), N > 0 for N clauses; at most 2^60 (no overflow)
pred cap i:int, o:int.
cap N M :- if (N > 1152921504606846976) (M = 1152921504606846976) (M = N).
% or_cnf_opt and and_cnf_opt of Tauto.v
pred c-or i:int, i:int, o:int.
c-or 0 _ 0 :- !.
c-or _ 0 0 :- !.
c-or -1 G G :- !.
c-or F -1 F :- !.
c-or F G R :- if (F > 1152921504606846976 div G) (R = 1152921504606846976) (R is F * G).
pred c-and i:int, i:int, o:int.
c-and -1 _ -1 :- !.
c-and _ -1 -1 :- !.
c-and 0 G G :- !.
c-and F 0 F :- !.
c-and F G R :- cap {calc (F + G)} R.
pred negb i:bool, o:bool.
negb tt ff.
negb ff tt.
% the comparisons of integers that lia reads (after zify)
pred int-rel i:gref.
int-rel GR :- std.mem! [{{:gref BinInt.Z.le}}, {{:gref BinInt.Z.lt}}, {{:gref BinInt.Z.ge}}, {{:gref BinInt.Z.gt}},
  {{:gref le}}, {{:gref lt}}, {{:gref ge}}, {{:gref gt}},
  {{:gref BinNat.N.le}}, {{:gref BinNat.N.lt}}, {{:gref BinNat.N.ge}}, {{:gref BinNat.N.gt}},
  {{:gref BinPos.Pos.le}}, {{:gref BinPos.Pos.lt}}, {{:gref BinPos.Pos.ge}}, {{:gref BinPos.Pos.gt}}] GR.
pred int-type i:term.
int-type T :- std.mem! [{{ BinNums.Z }}, {{ nat }}, {{ BinNums.N }}, {{ BinNums.positive }}, {{ bool }}] T.
% [cnf P F N]: the size of xcnf P F (P = tt for the goal, ff for a
% hypothesis, as tauto_checker runs xcnf true on hypotheses -> goal)
pred cnf i:bool, i:term, o:int.
cnf P {{ lp:A /\ lp:B }} N :- !, cnf P A NA, cnf P B NB,
  if (P = tt) (c-and NA NB N) (c-or NA NB N).
cnf P {{ lp:A \/ lp:B }} N :- !, cnf P A NA, cnf P B NB,
  if (P = tt) (c-or NA NB N) (c-and NA NB N).
cnf P {{ lp:A <-> lp:B }} N :- !, negb P Q,
  cnf Q A NA1, cnf ff B NB1, cnf P A NA2, cnf tt B NB2,
  c-and NA1 NB1 N1, c-and NA2 NB2 N2, c-or N1 N2 N.
cnf P {{ ~ lp:A }} N :- !, negb P Q, cnf Q A N.
cnf P (prod _ A (_\ B)) N :- !, negb P Q, cnf Q A NA, cnf P B NB,
  if (P = tt) (c-or NA NB N) (c-and NA NB N).
cnf tt {{ True }} 0 :- !.
cnf ff {{ True }} -1 :- !.
cnf tt {{ False }} -1 :- !.
cnf ff {{ False }} 0 :- !.
% x = y: two cases in the goal (x < y, x > y), one in a hypothesis
cnf P (app [global EQ, T, _, _]) N :- EQ = {{:gref eq}}, int-type T, !,
  if (P = tt) (N = 2) (N = 1).
cnf _ (app [global GR, _, _]) 1 :- int-rel GR, !.
cnf _ _ -1.
% the functions zify specifies by cases (micromega/ZifyInst.v): the
% number of cases of each
pred spec-fun i:gref, o:int.
spec-fun GR 3 :- GR = {{:gref BinInt.Z.sgn}}, !.
spec-fun GR 2 :- std.mem! [{{:gref BinInt.Z.abs}}, {{:gref BinInt.Z.max}}, {{:gref BinInt.Z.min}},
  {{:gref BinInt.Z.to_nat}}, {{:gref BinInt.Z.abs_nat}}, {{:gref BinInt.Z.to_N}}, {{:gref BinInt.Z.abs_N}}, {{:gref BinInt.Z.to_pos}},
  {{:gref PeanoNat.Nat.sub}}, {{:gref PeanoNat.Nat.pred}}, {{:gref PeanoNat.Nat.max}}, {{:gref PeanoNat.Nat.min}},
  {{:gref BinNat.N.sub}}, {{:gref BinNat.N.pred}}, {{:gref BinNat.N.max}}, {{:gref BinNat.N.min}},
  {{:gref BinPos.Pos.sub}}, {{:gref BinPos.Pos.pred}}, {{:gref BinPos.Pos.max}}, {{:gref BinPos.Pos.min}},
  {{:gref BinInt.Z.div}}, {{:gref BinInt.Z.modulo}}, {{:gref BinInt.Z.quot}}, {{:gref BinInt.Z.rem}},
  {{:gref PeanoNat.Nat.div}}, {{:gref PeanoNat.Nat.modulo}}, {{:gref BinNat.N.div}}, {{:gref BinNat.N.modulo}}] GR.
% [specs T S0 S]: the distinct applications of those functions in T, not
% under a binder (zify.ml, spec_of_term), added to S0
pred specs i:term, i:list term, o:list term.
specs (app [HD|Args] as T) S0 S :- !,
  std.fold Args S0 specs S1,
  if (HD = global GR, spec-fun GR _, not (std.exists S1 (same_term T)))
     (S = [T|S1]) (S = S1).
specs _ S S.
pred spec-cases i:term, o:int.
spec-cases (app [global GR|_]) N :- spec-fun GR N.
% the hypotheses that are propositions
pred prop-type i:term.
prop-type Ty :- coq.typecheck Ty S ok, S = sort prop.
pred ctx-type i:prop, o:term.
ctx-type (decl _ _ Ty) Ty.
ctx-type (def _ _ Ty _) Ty.
% [intro-stats Hs G Cases Hyps]: zify's intros, then the counts
pred intro-stats i:list term, i:term, o:int, o:int.
intro-stats Hs (prod N A B) C H :- !,
  if (prop-type A) (Hs1 = [A|Hs]) (Hs1 = Hs),
  pi x\ decl x N A => intro-stats Hs1 (B x) C H.
intro-stats Hs G C H :-
  std.map {std.filter Hs prop-type} (cnf ff) HN,
  std.filter HN (n\ not (n = -1)) Read, std.length Read H,
  std.fold [G|Hs] [] specs Sp, std.map Sp spec-cases SN,
  cnf tt G GN,
  std.fold {std.append HN SN} GN (n\a\b\ c-or n a b) C.
% log2 of the cases, rounded up: [log2up C P K L], P = 2^K
pred log2up i:int, i:int, i:int, o:int.
log2up C P K K :- C =< P, !.
log2up C P K L :- log2up C {calc (P * 2)} {calc (K + 1)} L.
pred stats i:goal-ctx, i:term, o:int, o:int, o:int.
stats Ctx Ty S C H :-
  std.map {std.filter Ctx (d\ sigma T\ ctx-type d T)} ctx-type Ts,
  intro-stats {std.rev Ts} Ty C H,
  if (C > 0) (log2up C 1 0 S) (S = 0).
solve (goal Ctx _ Ty _ [int K, int M]) _ :- !,
  stats Ctx Ty S C H,
  if (S > K) (coq.ltac.fail 0 "lia_guard:" S "case splits (" C "cases), at most" K) true,
  if (H > M) (coq.ltac.fail 0 "lia_guard:" H "hypotheses, at most" M) true.
solve (goal Ctx _ Ty _ [str "stats"]) _ :- !,
  stats Ctx Ty S C H, coq.say "LIA_STATS splits" S "cases" C "hyps" H.
% the counts compared with S, C, H (tests: lia_guard_check.v)
solve (goal Ctx _ Ty _ [str "expect", int S, int C, int H]) _ :- !,
  stats Ctx Ty S1 C1 H1,
  if (S1 = S, C1 = C, H1 = H) true
     (coq.ltac.fail 0 "lia_guard: counts" S1 C1 H1 "expected" S C H).
% the same, the line starting with a prefix (a tool may show only some lines)
solve (goal Ctx _ Ty _ [str "stats", str P]) _ :- !,
  stats Ctx Ty S C H, coq.say P "LIA_STATS splits" S "cases" C "hyps" H.
}}.
Ltac lia_guard := elpi lia_guard 18 16.
Ltac lia_stats := elpi lia_guard "stats".
(* the counts compared with S, C, H (tests: lia_guard_check.v) *)
Tactic Notation "lia_expect" int(s) int(c) int(h) :=
  elpi lia_guard "expect" ltac_int:(s) ltac_int:(c) ltac_int:(h).
(* lia and nia behind the guard *)
Ltac guarded_lia := lia_guard; lia.
Ltac guarded_nia := lia_guard; nia.

(* itauto (coq-itauto): a reflexive SAT solver for propositional logic, run
   for the word tauto: tauto may run for minutes on goals that itauto
   closes at once.  With the flag Itauto Classic, itauto reasons
   classically when the classical axiom is loaded, as tauto does *)
From Stdlib Require Import Lra Ring Field.
From Cdcl Require Import Itauto.
#[export] Set Itauto Classic.

(* The tactics that the words of tactics.elpi mean, in a justification
   *N*{.just} or in a header's by: word_N is the tactic the justification
   word N means, for cyp and xtext alike (cyp declares
   CypJustification "N" := word_N. at the end of cyp/vernac/Cyp.v; xtext
   runs word_N for the steps it justifies by N, xtext/ExtractText.v).  The
   bound of each: cyp/README.md, "Deterministic bounds". *)
(* lia and nia behind lia_guard (above) *)
Ltac word_lia := guarded_lia.          Ltac word_nia := guarded_nia.
Ltac word_lra := lra.                  Ltac word_nra := nra.
Ltac word_ring := ring.                Ltac word_field := field.
Ltac word_tauto := itauto auto.        Ltac word_auto := auto.
Ltac word_easy := easy.                Ltac word_reflexivity := reflexivity.
Ltac word_assumption := assumption.    Ltac word_congruence := congruence.
(* firstorder, bounded (above): firstorder has no bound (on a condition of
   xtext's half_le it ran over 30 s and took up to 7 GB) *)
Ltac word_firstorder := bounded_firstorder.
(* arith: the word xtext gives to a step whose conclusion is arithmetic
   (an equality or an order on nat, Z, N or R), closed by lia or by tauto *)
Ltac word_arith := first [ guarded_lia | itauto auto ].
