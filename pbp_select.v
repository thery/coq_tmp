(* From a selection in the goal to the pattern of pbp.

   The interface of a proof by pointing shows the goal and lets one
   select a subterm of it; the goal display tags each printed subterm with
   its path (Rocq's Set Printing Subterm Paths), and the interface sends
   the path of the selected one, in the conclusion or in the type of a
   hypothesis.  The tactic below turns it into the pbp call to insert in
   the script:

     Goal a + b = b + a.        elpi pbp_pattern "2.1".
                                prints  pbp [X in X + _ = _].

   A selection in a hypothesis H generalizes it (move: H) and the pattern
   is the one of the goal forall H, conclusion.  The paths, the patterns,
   the fallback chain when a subterm cannot be selected as it is, and the
   names of the variables of the patterns are those of subterm_pattern.v.
   This file adds the selections: their parts (the hypotheses and the
   conclusion), the selections of binder names, and the point-in value
   that the pointing actions (point_actions.v) are given. *)

From Stdlib Require Import ssreflect.
From elpi Require Import elpi.
From coq_tmp Require Export pbp subterm_pattern.

Elpi Db pbp_select.db lp:{{ }}.
Elpi Accumulate pbp_select.db File subterm_pattern.elpi.
Elpi Accumulate pbp_select.db lp:{{

/* ---------------- Selections ---------------- */

kind sel type.
type sel-goal list int -> sel.          % a path in the conclusion
type sel-hyp string -> list int -> sel. % a path in the type of a hypothesis

% [is-path-string S] S is written as a path ("" or starting with a digit)
pred is-path-string i:string.
is-path-string "" :- !.
is-path-string S :- rex.match "^[0-9]" S.

% [parse-sels As Sels] the arguments As are the selections Sels: "P" (a
% path in the conclusion) or "H" "P" (a path in the hypothesis H)
pred parse-sels i:list argument, o:list sel.
parse-sels [] [] :- !.
parse-sels [str P | As] [sel-goal Q | Sels] :- is-path-string P, !,
  path-of-string P Q, parse-sels As Sels.
parse-sels [str H, str P | As] [sel-hyp H Q | Sels] :- is-path-string P, !,
  path-of-string P Q, parse-sels As Sels.
parse-sels _ _ :-
  coq.ltac.fail 0 {msg "a selection is \"P\" (a path in the conclusion, \"i.j.k\", \"\" for the root) or \"H\" \"P\" (a path in the hypothesis H)"}.

% [hyp-of Ctx H V T] H is the name of the hypothesis V of type T in Ctx
% (not a local definition)
pred hyp-of i:goal-ctx, i:string, o:term, o:term.
hyp-of Ctx H V T :- std.mem Ctx (decl V N T), coq.name->id N H, !.
hyp-of Ctx H _ _ :- std.mem Ctx (def _ N _ _), coq.name->id N H, !,
  coq.ltac.fail 0 {msg "the hypothesis"} H "is a definition".
hyp-of _ H _ _ :- coq.ltac.fail 0 {msg "no hypothesis"} H.

% [ctx-names Ctx Ns] Ns are the names of the hypotheses of Ctx (the last
% one first)
pred ctx-names i:goal-ctx, o:list string.
ctx-names Ctx Ns :-
  std.map-filter Ctx (d\ h\ sigma V N T B\ (d = decl V N T ; d = def V N T B),
                         coq.name->id N h) Ns.

% [sel-hyps Ctx Sels Hs] Hs are the hypotheses of the selections Sels, in
% the order of the context (the oldest first)
pred sel-hyps i:goal-ctx, i:list sel, o:list string.
sel-hyps Ctx Sels Hs :-
  ctx-names Ctx Ns,
  std.filter Ns (h\ std.exists Sels (s\ sigma P\ s = sel-hyp h P)) Hs0,
  % the context of a goal lists its youngest hypothesis first
  std.rev Hs0 Hs.

% [ones N L] L is the path through N products to their body: N times 2
pred ones i:int, o:list int.
ones 0 [] :- !.
ones N [2|L] :- N1 is N - 1, ones N1 L.

% [revert Ctx Hs G C] C is G with the hypotheses Hs generalized (as
% move: Hs does): forall H1 .. Hn, G
pred revert i:goal-ctx, i:list string, i:term, o:term.
revert _ [] G G.
revert Ctx [H|Hs] G (prod N T F) :-
  hyp-of Ctx H V T, coq.id->name H N, revert Ctx Hs G C,
  pi x\ (copy V x :- !) => copy C (F x).

kind part type.
% [part B T] a part of the generalized goal: the hypothesis or the
% conclusion T at path B
type part list int -> term -> part.

% [parts Ctx Hs G Ps] Ps are the parts of the goal G with the hypotheses
% Hs generalized: the hypotheses, then the conclusion
pred parts i:goal-ctx, i:list string, i:term, o:list part.
parts Ctx Hs G Ps :-
  std.map-i Hs (i\ h\ p\ sigma B0 B V T\ ones i B0, std.append B0 [1] B,
                        hyp-of Ctx h V T, p = part B T)
    PHs,
  std.length Hs N, ones N BG,
  std.append PHs [part BG G] Ps.

kind loc type.
% [loc P I P0] a selection: the subterm at path P of the generalized goal,
% in its part number I (the hypotheses, then the conclusion), at path P0 of
% that part
type loc list int -> int -> list int -> loc.

% [loc-path L P] P is the path of the selection L in the generalized goal
pred loc-path i:loc, o:list int.
loc-path (loc P _ _) P.

% [locate Ctx Hs Ps Sel L W] the selection Sel is L; W is the text of the
% subterm if the selection had to be widened to it, "" otherwise
pred locate i:goal-ctx, i:list string, i:list part, i:sel, o:loc,
            o:string.
locate Ctx Hs Ps (sel-goal P0) (loc P N P1) W :- !,
  std.length Hs N, std.nth N Ps Part, locate-in Ctx (bm-goal 0) Part P0 P P1 W.
locate Ctx Hs Ps (sel-hyp H P0) (loc P I P1) W :-
  std.length Hs N, std.iota N Is, std.mem Is I, std.nth I Hs H, !,
  std.nth I Ps Part, locate-in Ctx bm-hyp Part P0 P P1 W.
% (no hypothesis H: hyp-of fails with the error)
locate Ctx _ _ (sel-hyp H _) _ _ :- hyp-of Ctx H _ _, !, fail.

% [locate-in Ctx M Part P0 P P1 W] the path P0 of the part Part selects
% its subterm at path P1, at path P of the generalized goal: a binder name
% selects its binder (or the nearest subterm above it printed as a whole),
% with a warning, unless the action takes names (paths-keep-names); any
% other path is the one of the fallback chain (path-pattern)
pred locate-in i:goal-ctx, i:bmode, i:part, i:list int, o:list int,
               o:list int, o:string.
locate-in Ctx M (part B T) P0 P P1 W :-
  ctx-names Ctx Names, string-of-path P0 S,
  (name-at T P0 K, not (paths-keep-names), !,
   parent P0 Q, printing-of T Pr, widen-from Names M T Pr Q P1 _ _,
   text-at-names Names M P1 T W1,
   (P1 = Q, !, W is W1 ^ " (a binder name: the whole " ^ K ^ " is selected)" ;
    W is W1 ^ " (a binder name)")
   ; name-at T P0 _, !, P1 = P0, W = ""
   ; (path-of T P0, ! ;
      through-name T P0, !, coq.ltac.fail 0 {msg "the path"} S "goes through a binder name" ;
      coq.ltac.fail 0 {msg "no subterm at the path"} S),
     path-pattern Names M T P0 P1 _ W),
  std.append B P1 P.

% [paths-keep-names] an action handles the selection of a binder name
% itself (point_actions.v: point-action-names): the path stays at the name
pred paths-keep-names.

/* ---------------- The selections, resolved ----------------
   What the actions of point_actions.v are given (and pbp_pattern uses) */

kind point-in type.
% [point-in Names Hs C Parts Ls] selections in a goal: Names are the
% names of its hypotheses, Hs the hypotheses the selections are in
% (generalized, in the order of the context), C the goal with Hs
% generalized, Parts its parts, Ls the selections (in the order given)
type point-in list string -> list string -> term -> list part -> list loc ->
              point-in.

% [point-resolve Ctx G Sels In Ws] the selections Sels of the goal G
% (context Ctx) are In; Ws are the texts of the subterms that selections
% were widened to
pred point-resolve i:goal-ctx, i:term, i:list sel, o:point-in,
                   o:list string.
point-resolve Ctx G Sels (point-in Names Hs C Parts Ls) Ws :-
  ctx-names Ctx Names,
  sel-hyps Ctx Sels Hs, revert Ctx Hs G C, parts Ctx Hs G Parts,
  std.map Sels (s\ lw\ sigma L W\ locate Ctx Hs Parts s L W, lw = pr L W)
    LWs,
  std.map LWs fst Ls, std.map-filter LWs (lw\ w\ lw = pr _ w, not (w = "")) Ws,
  std.map Ls loc-path Ps,
  (nested Ps, !,
   coq.ltac.fail 0 {msg "the two selections are the same subterm or one is inside the other"} ; true).

% [nested Ps] two of the paths Ps are the same or one is inside the other
pred nested i:list (list int).
nested Ps :-
  std.mem Ps P, std.mem Ps Q, not (P == Q), std.appendR P _ Q.
nested [P, P].

% [point-names In Ns] Ns are the names of the hypotheses of the goal
pred point-names i:point-in, o:list string.
point-names (point-in Ns _ _ _ _) Ns.

% [point-hyps In Hs] Hs are the hypotheses the selections are in, in the
% order of the context (none for selections in the conclusion)
pred point-hyps i:point-in, o:list string.
point-hyps (point-in _ Hs _ _ _) Hs.

% [point-count In N] there are N selections
pred point-count i:point-in, o:int.
point-count (point-in _ _ _ _ Ls) N :- std.length Ls N.

% [point-pattern In Pat] Pat is the pattern of the selections in the goal
% with their hypotheses generalized (the one of pbp): positional, X alone
% under the binders of the logical skeleton (subterm_pattern.v)
pred point-pattern i:point-in, o:string.
point-pattern (point-in Names Hs C _ Ls) Pat :-
  std.map Ls loc-path Ps, std.length Hs N,
  pattern-positional => pattern-of Names (bm-goal N) Ps C Pat.

% [point-revert In M] M is the tactic that generalizes the hypotheses of
% the selections, "move: H1 H2; ", or "" if there are none
pred point-revert i:point-in, o:string.
point-revert (point-in _ [] _ _ _) "" :- !.
point-revert (point-in _ Hs _ _ _) M :-
  std.string.concat " " Hs HsS, M is "move: " ^ HsS ^ "; ".

% [point-part In I] the selections are all in the part number I
pred point-part i:point-in, o:int.
point-part (point-in _ _ _ _ [loc _ I _ | Ls]) I :-
  std.forall Ls (l\ l = loc _ I _), !.
point-part _ _ :-
  coq.ltac.fail 0 {msg "the selections are not in the same hypothesis or both in the conclusion"}.

% [point-in-hyp In S] S is " in H" if the selections are in the hypothesis
% H, "" if they are in the conclusion
pred point-in-hyp i:point-in, o:string.
point-in-hyp (point-in _ Hs _ _ _ as In) S :-
  point-part In I, std.length Hs N,
  (I = N, !, S = "" ; std.nth I Hs H, S is " in " ^ H).

% [point-local-pattern In Pat] Pat is the pattern of the selections in
% their own part, the conclusion or the type of their hypothesis (as for
% rewrite ... in H)
pred point-local-pattern i:point-in, o:string.
point-local-pattern (point-in Names Hs _ Parts Ls as In) Pat :-
  point-part In I, std.nth I Parts (part _ T), std.length Hs N,
  (I = N, !, M = bm-goal 0 ; M = bm-hyp),
  std.map Ls (l\ p\ l = loc _ _ p) Ps,
  pattern-of Names M Ps T Pat.

% [point-text In I S] S is the text of the selection number I (from 0),
% on one line
pred point-text i:point-in, i:int, o:string.
point-text (point-in Names Hs C _ Ls) I S :-
  std.nth I Ls (loc P _ _), std.length Hs N, text-at-names Names (bm-goal N) P C S.

% [point-head In I GR] GR is the head of the selection number I (from 0):
% the selection is GR or an application of GR
pred point-head i:point-in, i:int, o:gref.
point-head (point-in _ _ C _ Ls) I GR :-
  std.nth I Ls (loc P _ _), head-at P C GR.

% [head-at P T GR] the subterm of T at path P is GR or an application of
% GR
pred head-at i:list int, i:term, o:gref.
head-at [] T GR :- head-gref T GR.
head-at [I|P] T GR :- kid-at T I (kid-head P GR).

% [kid-head P GR K] head-at in the immediate subterm K
pred kid-head i:list int, o:gref, i:kid.
kid-head P GR (kt T) :- head-at P T GR.
kid-head P GR (kb N Ty B) :- pi x\ decl x N Ty => head-at P (B x) GR.

% [head-gref T GR] T is GR or an application of GR
pred head-gref i:term, o:gref.
head-gref (global GR) GR.
head-gref (pglobal GR _) GR.
head-gref (app [H|_]) GR :- head-gref H GR.

/* ---------------- The pbp call ---------------- */

% [pbp-line Ctx G Sels Line Ws] Line is the pbp call for the selections
% Sels in the goal G (context Ctx); Ws are the texts of the subterms that
% selections were widened to
pred pbp-line i:goal-ctx, i:term, i:list sel, o:string, o:list string.
pbp-line Ctx G Sels Line Ws :-
  std.length Sels K,
  ((K = 1 ; K = 2), ! ;
   coq.ltac.fail 0 {msg "one selection (pointing) or two (linking)"}),
  point-resolve Ctx G Sels In Ws,
  point-pattern In Pat, point-revert In Move,
  Line is Move ^ "pbp " ^ Pat ^ ".".

}}.

(* [elpi pbp_pattern Sel ...] prints the pbp call for the selections, one
   (pointing) or two (linking); a selection is ["P"], the subterm at path
   P of the conclusion, or ["H" "P"], the one of the type of the
   hypothesis H ("i.j.k", "" for the whole part).  A subterm that cannot
   be selected is widened (subterm_pattern.v), with a warning
   (pbp-widened).  The goal is unchanged. *)
Elpi Tactic pbp_pattern.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  (tool-name "pbp_pattern" => (
     parse-sels Args Sels, pbp-line Ctx Ty Sels Line Ws,
     msg "the selection is widened to" M)),
  std.forall Ws (w\ coq.warning "pbp" "pbp-widened" M w),
  coq.say Line.
}}.

(* [elpi pbp_pattern_expect Line Ws Sel ...], for the tests: fails unless
   pbp_pattern gives the line Line, with the widened subterms Ws (separated
   by " / ", "" for none) *)
Elpi Tactic pbp_pattern_expect.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ [str Exp, str ExpW | Args] as G) [seal G] :-
  (tool-name "pbp_pattern" => (parse-sels Args Sels, pbp-line Ctx Ty Sels Line Ws)),
  std.string.concat " / " Ws W,
  ((Line = Exp, W = ExpW), ! ;
   coq.ltac.fail 0 "pbp_pattern_expect: got" Line W "expected" Exp ExpW).
}}.
