(* Selections given by character ranges, for an interface that does not
   tag the printed goal with paths: [elpi point_run "Name" S E] runs the
   action Name (point_actions.v) on the characters S to E (excluded) of
   the printed conclusion, [H S E] on those of the printed type of the
   hypothesis H; the characters that are not blanks are counted, from 0;
   an empty range (S = E) is a click on the character S.

   A range is turned into a path: the one of the smallest printed subterm
   whose text contains it (the less deep one if two have the same text);
   then point_run_path's pipeline runs on the paths.  A range that is not
   exactly that subterm (with or without its parentheses) is widened to
   it, with a warning (pbp-widened). *)

From coq_tmp Require Export point_actions.

Elpi Accumulate pbp_select.db lp:{{

kind range type.
type range-goal int -> int -> range.          % a range in the conclusion
type range-hyp string -> int -> int -> range. % one in the type of a hypothesis

% [parse-ranges As Rs] the arguments As are the ranges Rs: S E or H S E
pred parse-ranges i:list argument, o:list range.
parse-ranges [] [] :- !.
parse-ranges [int S, int E | As] [range-goal S E | Rs] :- !, parse-ranges As Rs.
parse-ranges [str H, int S, int E | As] [range-hyp H S E | Rs] :- !,
  parse-ranges As Rs.
parse-ranges _ _ :-
  coq.ltac.fail 0 {msg "a selection is S E (a range in the conclusion) or H S E (a range in the hypothesis H)"}.

% [range-sel Ctx G R Sel W] the range R of the goal G is the path selection
% Sel, W being the text of the subterm if the range was widened to it
pred range-sel i:goal-ctx, i:term, i:range, o:sel, o:string.
range-sel _ G (range-goal S E) (sel-goal P) W :- range-path G S E P W.
range-sel Ctx _ (range-hyp H S E) (sel-hyp H P) W :-
  hyp-of Ctx H _ T, range-path T S E P W.

% [range-path T S E P W] the range [S, E) of the printed T is its subterm
% at path P, the smallest printed one that contains it (a click S = S
% contains the character S); W as in range-sel
pred range-path i:term, i:int, i:int, o:list int, o:string.
range-path _ S E _ _ :- E < S, !,
  coq.ltac.fail 0 {msg "the range"} S E "ends before it starts".
range-path T S E P W :-
  (E = S, !, E1 is S + 1 ; E1 = E), printing-of T Pr,
  std.findall (range-of T Pr P_ S_ E_ L_) Rs,
  std.filter Rs (r\ sigma S2 E2\ r = range-of _ _ _ S2 E2 _, S2 =< S, E1 =< E2) Cs,
  (Cs = [C|Cs1], !,
   std.fold Cs1 C (a\ b\ c\ sigma La Lb\ a = range-of _ _ _ _ _ La,
     b = range-of _ _ _ _ _ Lb, (Lb < La, !, c = b ; c = a)) Best ;
   coq.ltac.fail 0 {msg "the range"} S E "is not in the printed term"),
  Best = range-of _ _ P S0 E0 _,
  ((E = S ; S = S0, E = E0 ; range-of-text T Pr P Txt, starts-with "(" Txt,
    S is S0 + 1, E is E0 - 1), !, W = "" ; text-at P T W).

% [range-of T Pr P S E L] the subterm at path P of T is printed as a whole
% from the character S to E (L = E - S), the root first, on backtracking
pred range-of i:term, i:printing, o:list int, o:int, o:int, o:int.
range-of T Pr P S E L :- path-of T P, whole-text T Pr P Before Txt,
  cp-length Before S, cp-length Txt L, E is S + L.

% [range-of-text T Pr P Txt] Txt is the text of the subterm at path P
pred range-of-text i:term, i:printing, i:list int, o:string.
range-of-text T Pr P Txt :- whole-text T Pr P _ Txt.

% [point-run-ranges Ctx G Args Line Ws] point-run, the selections being
% ranges
pred point-run-ranges i:goal-ctx, i:term, i:list argument, o:string,
                      o:list string.
point-run-ranges Ctx G [str Name | As] Line Ws :- point-action Name K _ Impl, !,
  parse-ranges As Rs,
  std.map Rs (r\ sw\ sigma Sel W\ range-sel Ctx G r Sel W, sw = pr Sel W) SWs,
  std.map SWs fst Sels,
  std.map-filter SWs (sw\ w\ sw = pr _ w, not (w = "")) Ws0,
  point-run-sels Ctx G Name K Impl Sels Line Ws1, std.append Ws0 Ws1 Ws.
point-run-ranges Ctx G Args Line Ws :- point-run Ctx G Args Line Ws.
}}.

(* [elpi point_run "Name" Sel ...]: point_run_path for ranges [S E] or
   [H S E] *)
Elpi Tactic point_run.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  (tool-name "point_run" => (point-run-ranges Ctx Ty Args Line Ws,
                             msg "the selection is widened to" M)),
  std.forall Ws (w\ coq.warning "pbp" "pbp-widened" M w),
  coq.say Line.
}}.

(* [elpi point_run_expect "Name" Line Ws Sel ...], for the tests: fails
   unless point_run gives the line Line, with the widened subterms Ws
   (separated by " / ", "" for none) *)
Elpi Tactic point_run_expect.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ [str Name, str Exp, str ExpW | Args] as G) [seal G] :-
  (tool-name "point_run" => point-run-ranges Ctx Ty [str Name | Args] Line Ws),
  std.string.concat " / " Ws W,
  ((Line = Exp, W = ExpW), ! ;
   coq.ltac.fail 0 "point_run_expect: got" Line W "expected" Exp ExpW).
}}.
