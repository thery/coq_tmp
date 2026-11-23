(* Pointing actions: what an interface offers on a selection in the goal.

   An interface for proof by pointing shows the goal, lets one select a
   part of it (or two), and offers actions on the selection; an action
   writes the line to insert in the script.  The actions are declared in
   Rocq, by any loaded file; the interface only lists them and runs the
   chosen one:

     PointAction "Point" point "{revert}pbp {pattern}." "...".
     elpi point_actions.              prints the actions (JSON)
     elpi point_run "Point" 0 1.      prints the line, pbp [X in X + _ = _].

   A selection is the one of pbp_select.v: [S E], a range of the printed
   conclusion, or [H S E], one of the printed type of the hypothesis H, in
   characters that are not blanks.  An action is of kind [point] (one
   selection) or [link] (two).

   An action is an Elpi predicate (pred i:point-in, o:string) that is given
   the selections, resolved to subterms of the goal (point-in, see
   pbp_select.v), and gives the line; PointAction declares one from a
   template, a line with placeholders:

     {pattern}  the pattern of pbp, [X in ...] or [X Y in ...], in the goal
                where the hypotheses of the selections are generalized
     {revert}   the tactic that generalizes them, "move: H; ", or ""
     {local}    the pattern in the part of the goal the selections are in,
                the conclusion or the type of the hypothesis H
     {in}       " in H" if the selections are in the hypothesis H, else ""
     {head}     the constant that the (first) selection is, or that it is
                an application of
     {text}     the (first) selected subterm, as printed

   An action written in Elpi is declared by accumulating a clause of
   point-action in pbp_select.db (point_actions_test.v has one). *)

From Stdlib Require Import ssreflect.
From elpi Require Export elpi.
From coq_tmp Require Export pbp_select.

Elpi Accumulate pbp_select.db lp:{{

/* ---------------- The actions ---------------- */

kind point-kind type.
type point point-kind.   % one selection
type link point-kind.    % two selections

% [point-kind-name K S N] the kind K is written S and takes N selections
pred point-kind-name o:point-kind, o:string, o:int.
point-kind-name point "point" 1.
point-kind-name link "link" 2.

% [point-action Name Kind Doc Impl] the action Name, of kind Kind,
% described by Doc, gives the line Impl In Line for the selections In
pred point-action o:string, o:point-kind, o:string,
                  o:(pred i:point-in, o:string).

/* ---------------- Templates ---------------- */

kind tpart type.
type tlit string -> tpart.    % a text
type thole string -> tpart.   % a placeholder {name}

% [tpl-parse S Ps] the template S is the parts Ps (fails if a { is not
% closed)
pred tpl-parse i:string, o:list tpart.
tpl-parse S Ps :- tpl-scan S 0 0 Ps.

% [tpl-scan S St I Ps] Ps are the parts of S from St, the text from St to
% I having no placeholder
pred tpl-scan i:string, i:int, i:int, o:list tpart.
tpl-scan S St I Ps :- I >= size S, !, tpl-lit S St I [] Ps.
tpl-scan S St I Ps :- "{" is substring S I 1, !,
  I1 is I + 1, tpl-close S I1 K,
  Name is substring S I1 (K - I1), K1 is K + 1,
  tpl-scan S K1 K1 Rest, tpl-lit S St I [thole Name | Rest] Ps.
tpl-scan S St I Ps :- I1 is I + 1, tpl-scan S St I1 Ps.

% [tpl-close S I K] the first } of S from I is at K
pred tpl-close i:string, i:int, o:int.
tpl-close S I _ :- I >= size S, !, fail.
tpl-close S I I :- "}" is substring S I 1, !.
tpl-close S I K :- I1 is I + 1, tpl-close S I1 K.

% [tpl-lit S St I Rest Ps] Ps is the text of S from St to I, then Rest
pred tpl-lit i:string, i:int, i:int, i:list tpart, o:list tpart.
tpl-lit _ St St Rest Rest :- !.
tpl-lit S St I Rest [tlit T | Rest] :- T is substring S St (I - St).

% [placeholder Name] Name is a placeholder of the templates
pred placeholder o:string.
placeholder "pattern".
placeholder "revert".
placeholder "local".
placeholder "in".
placeholder "head".
placeholder "text".

% [placeholder-value Name In V] the placeholder Name is V for the
% selections In
pred placeholder-value i:string, i:point-in, o:string.
placeholder-value "pattern" In V :- point-pattern In V.
placeholder-value "revert" In V :- point-revert In V.
placeholder-value "local" In V :- point-local-pattern In V.
placeholder-value "in" In V :- point-in-hyp In V.
placeholder-value "head" In V :-
  (point-head In 0 (const C), ! ;
   coq.ltac.fail 0 {msg "the selection is not a constant nor an application of a constant"}),
  coq.term->string (global (const C)) V0, rex.replace "^@" "" V0 V.
placeholder-value "text" In V :- point-text In 0 V.

% [point-template T In Line] Line is the template T for the selections In
pred point-template i:string, i:point-in, o:string.
point-template T In Line :-
  tpl-parse T Ps,
  std.map Ps (p\ s\ (p = tlit s ; sigma N\ p = thole N, placeholder-value N In s)) Ss,
  std.string.concat "" Ss Line.

/* ---------------- Listing ---------------- */

% [json-string S J] J is the JSON string of S
pred json-string i:string, o:string.
json-string S J :-
  json-chars S 0 Cs, std.string.concat "" Cs B, J is "\"" ^ B ^ "\"".

pred json-chars i:string, i:int, o:list string.
json-chars S I [] :- I >= size S, !.
json-chars S I [E|Es] :-
  C is substring S I 1, json-char C E, I1 is I + 1, json-chars S I1 Es.

pred json-char i:string, o:string.
json-char "\"" "\\\"" :- !.
json-char "\\" "\\\\" :- !.
json-char C E :- N is rhc C, N < 32, !,
  H is N div 16, L is N mod 16,
  std.nth H ["0","1"] HS,
  std.nth L ["0","1","2","3","4","5","6","7","8","9","a","b","c","d","e","f"] LS,
  E is "\\u00" ^ HS ^ LS.
json-char C C.

% [action-json A J] J is the JSON object of the action A
pred action-json i:prop, o:string.
action-json (point-action N K D _) J :-
  point-kind-name K KS _,
  json-string N NJ, json-string KS KJ, json-string D DJ,
  J is "{\"name\":" ^ NJ ^ ",\"kind\":" ^ KJ ^ ",\"doc\":" ^ DJ ^ "}".

% [actions-json J] J is the JSON array of the actions, in the order they
% were declared
pred actions-json o:string.
actions-json J :-
  std.findall (point-action N_ K_ D_ I_) As,
  std.map As action-json Js, std.string.concat "," Js B,
  J is "[" ^ B ^ "]".

/* ---------------- Running ---------------- */

% [point-run Ctx G Args Line Ws] Line is the line of the action and the
% selections given by Args, in the goal G (context Ctx); Ws are the texts
% of the subterms that selections were widened to
pred point-run i:goal-ctx, i:term, i:list argument, o:string,
               o:list string.
point-run _ _ [] _ _ :- !,
  coq.ltac.fail 0 {msg "the first argument is the name of an action (elpi point_actions lists them)"}.
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
point-run _ _ _ _ _ :-
  coq.ltac.fail 0 {msg "the first argument is the name of an action, a string"}.

}}.

(* [PointAction "Name" Kind "Template" "Doc"] declares the action Name, of
   kind point (one selection) or link (two), whose line is the template
   (the placeholders above), described by Doc (optional).  The actions are
   listed in the order of their declarations; a name is declared once. *)
Elpi Command PointAction.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
main [str Name, str K, str T] :- !, main [str Name, str K, str T, str ""].
main [str Name, str K, str T, str Doc] :- !,
  (point-kind-name Kind K _, ! ;
   coq.error "PointAction: the kind is point (one selection) or link (two), not" K),
  (point-action Name _ _ _, !,
   coq.error "PointAction: the action" Name "is already declared" ; true),
  (tpl-parse T Ps, ! ;
   coq.error "PointAction: a { is not closed in the template" T),
  std.forall Ps (p\ sigma N\ (p = thole N, !,
    (placeholder N, ! ;
     std.findall (placeholder N_) L, std.map L (c\ s\ sigma M\ c = placeholder M, s is "{" ^ M ^ "}") Ls,
     std.string.concat " " Ls LS,
     coq.error "PointAction: unknown placeholder" {calc ("{" ^ N ^ "}")} "in the template; the placeholders are" LS) ; true)),
  coq.elpi.accumulate _ "pbp_select.db"
    (clause _ _ (point-action Name Kind Doc (point-template T))).
main _ :-
  coq.error "PointAction: the arguments are \"Name\" point|link \"Template\" and, optionally, \"Doc\"".
}}.
Elpi Export PointAction.

(* [elpi point_actions] prints the actions, one message (a notice): a JSON
   array of objects {"name": ..., "kind": "point" | "link", "doc": ...}.
   The goal is unchanged. *)
Elpi Tactic point_actions.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ [] as G) [seal G] :- !, actions-json J, coq.say J.
solve _ _ :- coq.ltac.fail 0 "point_actions: no arguments".
}}.

(* [elpi point_run "Name" Sel ...] prints the line of the action Name for
   the selections (as for pbp_pattern: [S E] or [H S E]); a selection
   widened to a subterm gives a warning (pbp-widened) before the line.
   The goal is unchanged. *)
Elpi Tactic point_run.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  (tool-name "point_run" => (
     point-run Ctx Ty Args Line Ws,
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
  (tool-name "point_run" => point-run Ctx Ty [str Name | Args] Line Ws),
  std.string.concat " / " Ws W,
  ((Line = Exp, W = ExpW), ! ;
   coq.ltac.fail 0 "point_run_expect: got" Line W "expected" Exp ExpW).
}}.

(* [elpi point_actions_expect J], for the tests: fails unless point_actions
   prints J *)
Elpi Tactic point_actions_expect.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ [str Exp] as G) [seal G] :-
  actions-json J,
  (J = Exp, ! ; coq.ltac.fail 0 "point_actions_expect: got" J "expected" Exp).
}}.

(* ---------------- The actions declared here ---------------- *)

PointAction "Point" point "{revert}pbp {pattern}."
  "pbp: bring the selected subformula to the surface of the goal".
PointAction "Link" link "{revert}pbp {pattern}."
  "pbp: link the two selected subformulas".
PointAction "Simplify here" point "rewrite {local}/={in}."
  "simplify the selected subterm (ssreflect's rewrite /=, at the selection)".
PointAction "Unfold here" point "rewrite {local}/{head}{in}."
  "unfold the constant at the head of the selected subterm, in it".
