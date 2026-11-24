(* Pointing actions: what an interface offers on a selection in the goal.

   An interface for proof by pointing shows the goal, lets one select a
   part of it (or two), and offers actions on the selection; an action
   writes the line to insert in the script.  The actions are declared in
   Rocq, by any loaded file; the interface only lists them and runs the
   chosen one:

     PointAction "Point" point "{pre:revert}pbp {path:pbp}{post:revert}." "...".
     elpi point_actions.              prints the actions (JSON)
     elpi point_run "Point" 0 1.      prints the line, pbp [X in X + _ = _].

   A selection is the one of pbp_select.v: [S E], a range of the printed
   conclusion, or [H S E], one of the printed type of the hypothesis H, in
   characters that are not blanks.  An action is of kind [point] (one
   selection), [link] (two) or [show] (one: what it gives is a message to
   show, which point_run prints as it prints a line; the interface inserts
   nothing).  An action of kind show given two selections fails with the
   message of the other kinds (it takes 1 selection, not 2).

   An action is an Elpi predicate (pred i:point-in, o:string) that is given
   the selections, resolved to subterms of the goal (point-in, see
   pbp_select.v), and gives the line; PointAction declares one from a
   template, a line with placeholders:

     {path:M}   where the selections are, written by the path method M
                (pbp: [X in X + _ = _], occ: {2}, at: 2, path: [2, 1]), in
                the goal where the hypotheses of the selections are
                generalized
     {local:M}  the same in the part the selections are in, the conclusion
                or the type of their hypothesis
     {pre:S}    what the hypothesis strategy S (revert: "move: H; ",
                in: "", forward: "have H' := H; ") writes before the core
     {post:S}   what it writes after the core (revert: "", in: " in H",
                forward: " in H'")
     {head}     the constant that the (first) selection is, or that it is
                an application of
     {text}     the (first) selected subterm, as printed
     {pattern} {local} {revert} {in}: {path:pbp} {local:pbp} {pre:revert}
                {post:in}, their former names

   Path methods (point-path) and strategies (point-hyp-strategy) are
   declared by Elpi clauses in pbp_select.db, as below.

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
type show point-kind.    % one selection; its "line" is a message to show

% [point-kind-name K S N] the kind K is written S and takes N selections
pred point-kind-name o:point-kind, o:string, o:int.
point-kind-name point "point" 1.
point-kind-name link "link" 2.
point-kind-name show "show" 1.

% [point-action Name Kind Doc Impl] the action Name, of kind Kind,
% described by Doc, gives the line Impl In Line for the selections In
pred point-action o:string, o:point-kind, o:string,
                  o:(pred i:point-in, o:string).

% [point-action-origin Name Lib Line] the action Name was declared by
% PointAction in the library Lib, at the line Line (none for the actions
% declared by an Elpi clause)
pred point-action-origin o:string, o:string, o:int.

/* ---------------- Path methods ----------------
   A path method writes where the selections are, in a form a tactic
   reads: pbp's pattern [X in ...], ssreflect's occurrences {2}, ... */

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

% [scope-term Sc In T Ps] T is the term the selections In are in, for the
% scope Sc, and Ps their paths in T
pred scope-term i:point-scope, i:point-in, o:term, o:list (list int).
scope-term path-goal (point-in _ _ C _ Ls) C Ps :- std.map Ls loc-path Ps.
scope-term path-part (point-in _ _ _ Parts Ls as In) T Ps :-
  point-part In I, std.nth I Parts (part _ T _),
  std.map Ls (l\ p\ l = loc _ _ p) Ps.

% [term-at P T R] R is the subterm of T at path P; it fails if R uses a
% variable bound in T
pred term-at i:list int, i:term, o:term.
term-at [] T T.
term-at [I|P] T R :- kids T Ks, std.nth I Ks K, kid-term P K R.

pred kid-term i:list int, i:kid, o:term.
kid-term P (kt T) R :- term-at P T R.
kid-term P (kb _ _ B) R :- pi x\ term-at P (B x) R.

% [occurrences Sc In Ns] the selections In are the occurrences number Ns
% (from 1) of their subterm, in the scope Sc: the subterms equal to it,
% left to right (heads before arguments, binder types before bodies), as
% ssreflect's {n} and Rocq's "at n" count them
pred occurrences i:point-scope, i:point-in, o:list int.
occurrences Sc In Ns :-
  scope-term Sc In T Ps,
  msg "the selection uses a variable bound in the goal: it has no occurrence number" M1,
  std.map Ps (p\ r\ (term-at p T r, ! ; coq.ltac.fail 0 M1)) [R|Rs],
  (std.forall Rs (r\ r == R), ! ;
   coq.ltac.fail 0 {msg "the two selections are not the same term: they have no common occurrence numbers"}),
  std.findall (path-of T P_) Sols,
  std.map-filter Sols (s\ p\ sigma R1\ s = path-of T p, term-at p T R1, R1 == R)
    Occs,
  std.map Ps (p\ n\ occurrence-number Occs p 1 n) Ns0,
  (Ns0 = [A, B], A > B, !, Ns = [B, A] ; Ns = Ns0).

pred occurrence-number i:list (list int), i:list int, i:int, o:int.
occurrence-number [P|_] P N N :- !.
occurrence-number [_|Ps] P N M :- N1 is N + 1, occurrence-number Ps P N1 M.

% [ints-text Ns S] S is the numbers Ns separated by spaces
pred ints-text i:list int, o:string.
ints-text Ns S :- std.map Ns (n\ s\ s is int_to_string n) Ss,
  std.string.concat " " Ss S.

pred path-pbp i:point-scope, i:point-in, o:string.
path-pbp path-goal In S :- point-pattern In S.
path-pbp path-part In S :- point-local-pattern In S.

pred path-occ i:point-scope, i:point-in, o:string.
path-occ Sc In S :- occurrences Sc In Ns, ints-text Ns T, S is "{" ^ T ^ "}".

pred path-at i:point-scope, i:point-in, o:string.
path-at Sc In S :- occurrences Sc In Ns, ints-text Ns S.

pred path-raw i:point-scope, i:point-in, o:string.
path-raw Sc In S :-
  scope-term Sc In _ Ps,
  std.map Ps (p\ s\ sigma Ss B\ std.map p (n\ t\ t is int_to_string n) Ss,
                    std.string.concat ", " Ss B, s is "[" ^ B ^ "]") Ts,
  std.string.concat " " Ts S.

point-path "pbp" "pbp's pattern: [X in X + _ = _] ([X Y in ...] for two selections)" path-pbp.
point-path "occ" "ssreflect's occurrences of the selected term: {2} ({1 3} for two selections of the same term)" path-occ.
point-path "at" "Rocq's occurrences (unfold, pattern ... at n): 2 (1 3 for two)" path-at.
point-path "path" "the positions of the selections in the term, from its root (in an application the head is 0 and the arguments 1, 2, ...; in a binder its name is 0, its type 1 and its body 2): [1, 2] (two lists for two selections)" path-raw.

/* ---------------- Hypothesis strategies ----------------
   How an action on selections in hypotheses is written: what comes before
   the core of the line and what comes after it (before its final dot) */

% [point-hyp-strategy Name Doc Impl] the strategy Name, described by Doc,
% writes Impl In Pre Post around the core of the line, for the selections
% In (or fails with a message)
pred point-hyp-strategy o:string, o:string,
                        o:(pred i:point-in, o:string, o:string).

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

pred hyp-forward i:point-in, o:string, o:string.
hyp-forward In Pre Post :-
  one-hyp In H,
  (H = "", !, Pre = "", Post = "" ;
   point-names In Names, fresh-name {calc (H ^ "'")} Names 0 H1,
   Pre is "have " ^ H1 ^ " := " ^ H ^ "; ", Post is " in " ^ H1).

point-hyp-strategy "revert" "move the hypotheses to the goal first (move: H; ...), the core acts on the goal" hyp-revert.
point-hyp-strategy "in" "act in the hypothesis itself (... in H)" hyp-in.
point-hyp-strategy "forward" "act in a copy of the hypothesis (have H' := H; ... in H'), H stays" hyp-forward.

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

% [prefixed P S R] S is P followed by R
pred prefixed i:string, i:string, o:string.
prefixed P S R :- starts-with P S, R is substring S (size P) (size S - size P).

% [placeholder Name] Name is a placeholder of the templates: a fixed one,
% path:M or local:M for a path method M, pre:S or post:S for a strategy S
pred placeholder i:string.
placeholder N :- std.mem! ["pattern", "revert", "local", "in", "head", "text"] N, !.
placeholder N :- (prefixed "path:" N M ; prefixed "local:" N M), point-path M _ _, !.
placeholder N :- (prefixed "pre:" N S ; prefixed "post:" N S), point-hyp-strategy S _ _, !.

% [placeholders-text S] S describes the placeholders, for an error
pred placeholders-text o:string.
placeholders-text S :-
  std.findall (point-path M_ D_ I_) Ms, std.map Ms (c\ m\ c = point-path m _ _) MNs,
  std.findall (point-hyp-strategy N_ E_ J_) Ss, std.map Ss (c\ m\ c = point-hyp-strategy m _ _) SNs,
  std.string.concat ", " MNs MS, std.string.concat ", " SNs SS,
  S is "{pattern} {revert} {local} {in} {head} {text}, {path:M} {local:M} for a path method M (" ^ MS ^ "), {pre:S} {post:S} for a hypothesis strategy S (" ^ SS ^ ")".

% [placeholder-value Name In V] the placeholder Name is V for the
% selections In
pred placeholder-value i:string, i:point-in, o:string.
placeholder-value "pattern" In V :- !, placeholder-value "path:pbp" In V.
placeholder-value "local" In V :- !, placeholder-value "local:pbp" In V.
placeholder-value "revert" In V :- !, placeholder-value "pre:revert" In V.
placeholder-value "in" In V :- !, placeholder-value "post:in" In V.
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
   kind point (one selection), link (two) or show (one selection; the
   text is a message to show, not a line to insert), whose line is the template
   (the placeholders above), described by Doc (optional).  The actions are
   listed in the order of their declarations; a name is declared once. *)
Elpi Command PointAction.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
main [str Name, str K, str T] :- !, main [str Name, str K, str T, str ""].
main [str Name, str K, str T, str Doc] :- !,
  (point-kind-name Kind K _, ! ;
   coq.error "PointAction: the kind is point (one selection), link (two) or show (one, a message to show), not" K),
  (point-action Name _ _ _, !,
   coq.error "PointAction: the action" Name "is already declared" ; true),
  (tpl-parse T Ps, ! ;
   coq.error "PointAction: a { is not closed in the template" T),
  std.forall Ps (p\ sigma N\ (p = thole N, !,
    (placeholder N, ! ;
     placeholders-text LS,
     coq.error "PointAction: unknown placeholder" {calc ("{" ^ N ^ "}")} "in the template; the placeholders are" LS) ; true)),
  coq.env.current-path Path, std.string.concat "." Path Lib,
  (attributes As, std.mem As (attribute "elpi.loc" (leaf-loc Loc)), !,
   loc.fields Loc _ _ _ Line _ ; Line = 0),
  coq.elpi.accumulate _ "pbp_select.db"
    (clause _ _ (point-action Name Kind Doc (point-template T))),
  coq.elpi.accumulate _ "pbp_select.db"
    (clause _ _ (point-action-origin Name Lib Line)).
main _ :-
  coq.error "PointAction: the arguments are \"Name\" point|link|show \"Template\" and, optionally, \"Doc\"".
}}.
Elpi Export PointAction.

(* [PointActions] prints the actions declared at this point, in the order
   of their declarations, for a human reader: for each, its name, its
   kind, where it was declared, its template (or the Elpi predicate that
   implements it) and its doc.  A command: it works outside proofs too. *)
Elpi Accumulate pbp_select.db lp:{{
% [action-text A S] S describes the action A, on a few lines
pred action-text i:prop, o:string.
action-text (point-action N K D I) S :-
  point-kind-name K KS _,
  (point-action-origin N Lib Line, !,
   (Line > 0, !, Where is " in " ^ Lib ^ ", line " ^ int_to_string Line ;
    Where is " in " ^ Lib) ;
   Where = " by an Elpi clause"),
  (I = point-template T, !, Impl is "template: " ^ T ;
   term_to_string I P, Impl is "Elpi: " ^ P),
  (D = "", !, Doc = "" ; Doc is "\n  doc: " ^ D),
  S is N ^ " (" ^ KS ^ "), declared" ^ Where ^ "\n  " ^ Impl ^ Doc.

% [actions-text S] S describes the actions, in the order of their
% declarations
pred actions-text o:string.
actions-text S :-
  std.findall (point-action N_ K_ D_ I_) As,
  std.length As Nb,
  std.map As action-text Ts,
  std.string.concat "\n" Ts B,
  S is int_to_string Nb ^ " pointing action(s):\n" ^ B.
}}.
Elpi Command PointActions.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
main [] :- !, actions-text S, coq.say S.
main _ :- coq.error "PointActions: no arguments".
}}.
Elpi Export PointActions.

(* [PointPaths] and [PointStrategies] print the path methods and the
   hypothesis strategies declared at this point, in the order of their
   declarations: name, Elpi predicate, doc.  Commands: outside proofs too. *)
Elpi Accumulate pbp_select.db lp:{{
% [paths-text S] S describes the path methods
pred paths-text o:string.
paths-text S :-
  std.findall (point-path N_ D_ I_) Ps,
  std.map Ps (c\ t\ sigma N D I P\ c = point-path N D I, term_to_string I P,
                t is N ^ " (Elpi: " ^ P ^ ")\n  " ^ D) Ts,
  std.length Ps Nb, std.string.concat "\n" Ts B,
  S is "Path methods (" ^ int_to_string Nb ^ "), {path:M} or {local:M}:\n" ^ B.

% [strategies-text S] S describes the hypothesis strategies
pred strategies-text o:string.
strategies-text S :-
  std.findall (point-hyp-strategy N_ D_ I_) Ps,
  std.map Ps (c\ t\ sigma N D I P\ c = point-hyp-strategy N D I, term_to_string I P,
                t is N ^ " (Elpi: " ^ P ^ ")\n  " ^ D) Ts,
  std.length Ps Nb, std.string.concat "\n" Ts B,
  S is "Hypothesis strategies (" ^ int_to_string Nb ^ "), {pre:S} and {post:S}:\n" ^ B.
}}.
Elpi Command PointPaths.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
main [] :- !, paths-text S, coq.say S.
main _ :- coq.error "PointPaths: no arguments".
}}.
Elpi Export PointPaths.
Elpi Command PointStrategies.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
main [] :- !, strategies-text S, coq.say S.
main _ :- coq.error "PointStrategies: no arguments".
}}.
Elpi Export PointStrategies.

(* [Elpi point_text_expect What S], for the tests: fails unless the text
   of What (actions, paths, strategies) is S *)
Elpi Command point_text_expect.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
main [str W, str Exp] :-
  (W = "actions", actions-text S ; W = "paths", paths-text S ;
   W = "strategies", strategies-text S), !,
  (S = Exp, ! ; coq.error "point_text_expect: got" S "expected" Exp).
}}.

(* [elpi point_actions] prints the actions, one message (a notice): a JSON
   array of objects {"name": ..., "kind": "point" | "link" | "show", "doc": ...}.
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

(* ---------------- The actions declared here ----------------
   Point and Link; more actions (Simplify here, Unfold here, Name
   occurrence) are in point_actions_more.v *)

PointAction "Point" point "{pre:revert}pbp {path:pbp}{post:revert}."
  "pbp: bring the selected subformula to the surface of the goal".
PointAction "Link" link "{pre:revert}pbp {path:pbp}{post:revert}."
  "pbp: link the two selected subformulas".

(* ---------------- Seeing a selection ---------------- *)

(* [elpi point_show Sel ...] prints, for a human reader, what an action is
   given for the selections (as for point_run: [S E] or [H S E]): the
   point-in value, field by field, with the printed subterms of each part
   (shown P S E T: the subterm at path P is printed from the character S
   to E, as T).  The goal is unchanged. *)
Elpi Tactic point_show.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
pred show-path i:list int, o:string.
show-path P S :-
  std.map P (n\ s\ s is int_to_string n) Ss, std.string.concat ", " Ss B,
  S is "[" ^ B ^ "]".

pred show-strings i:list string, o:string.
show-strings L S :- std.string.concat ", " L B, S is "[" ^ B ^ "]".

pred show-shown i:shown, o:string.
show-shown (shown P S E T) R :-
  show-path P PS,
  R is "      shown " ^ PS ^ " " ^ int_to_string S ^ " " ^ int_to_string E ^ " \"" ^ T ^ "\"".

% [show-part Hs I P S] S describes the part number I
pred show-part i:list string, i:int, i:part, o:string.
show-part Hs I (part B T Shs) S :-
  std.length Hs N,
  (I = N, !, What = "the conclusion" ; std.nth I Hs H, What is "the type of " ^ H),
  coq.term->string T TS0, one-line TS0 TS, show-path B BS,
  std.map Shs show-shown Ls, std.string.concat "\n" Ls L,
  S is "    " ^ int_to_string I ^ ": part " ^ BS ^ " (" ^ What ^ "): " ^ TS ^ "\n" ^ L.

% [show-loc C L S] S describes the selection L of the goal C
pred show-loc i:term, i:loc, o:string.
show-loc C (loc P I P0) S :-
  show-path P PS, show-path P0 P0S, text-at P C Txt,
  (term-at P C T, !, term_to_string T TE ; TE = "(uses a variable bound in the goal)"),
  S is "    loc " ^ PS ^ " " ^ int_to_string I ^ " " ^ P0S ^ "\n      the subterm: " ^ Txt ^ "\n      in Elpi: " ^ TE.

pred show-in i:point-in, o:string.
show-in (point-in Names Hs C Parts Ls) S :-
  show-strings Names NS, show-strings Hs HS,
  coq.term->string C CS0, one-line CS0 CS,
  std.map-i Parts (show-part Hs) PSs, std.string.concat "\n" PSs PS,
  std.map Ls (show-loc C) LSs, std.string.concat "\n" LSs LS,
  S is "point-in\n  Names = " ^ NS ^ "\n  Hs = " ^ HS ^ "\n  C = " ^ CS ^
       "\n  Parts =\n" ^ PS ^ "\n  Ls =\n" ^ LS.

solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  (tool-name "point_show" => (
     parse-sels Args Sels, point-resolve Ctx Ty Sels In Ws,
     msg "the selection is widened to" M)),
  std.forall Ws (w\ coq.warning "pbp" "pbp-widened" M w),
  show-in In S, coq.say S.
}}.

(* ---------------- Selections given by paths ---------------- *)

Elpi Accumulate pbp_select.db lp:{{

% [point-action-names Name] the action Name handles a selection that is a
% binder name (a path ending at index 0 of a binder): point_run_path gives
% it the path of the name; the other actions get the binder, widened with
% a warning.  No action declared here does.
pred point-action-names o:string.

% [point-action-any-subterm Name] the action Name does not write a pattern:
% point_run_path gives it any subterm, even one whose pattern does not
% pass the check (as the actions of kind show)
pred point-action-any-subterm o:string.

% [point-run-paths Ctx G Args Line Ws] Line is the line of the action and
% the path selections given by Args (point_run_path), in the goal G; Ws
% are the texts of the subterms that selections were widened to
pred point-run-paths i:goal-ctx, i:term, i:list argument, o:string,
                     o:list string.
point-run-paths _ _ [] _ _ :- !,
  coq.ltac.fail 0 {msg "the first argument is the name of an action (elpi point_actions lists them)"}.
point-run-paths Ctx G [str Name | As] Line Ws :- !,
  (point-action Name K _ Impl, ! ;
   coq.ltac.fail 0 {msg "no action"} Name "(elpi point_actions lists them)"),
  parse-psels As Sels, std.length Sels N, point-kind-name K KS KN,
  (N = KN, ! ;
   coq.ltac.fail 0 {msg "the action"} Name "is of kind" KS "and takes" KN
     "selection(s), not" N),
  ((K = show ; point-action-any-subterm Name), !, NC = paths-no-check ;
   NC = paths-default),
  (point-action-names Name, !, (paths-keep-names, NC) => point-resolve-paths Ctx G Sels In Ws ;
   NC => point-resolve-paths Ctx G Sels In Ws),
  (Impl In Line, ! ;
   coq.ltac.fail 0 {msg "the action"} Name "does not apply to the selection").
point-run-paths _ _ _ _ _ :-
  coq.ltac.fail 0 {msg "the first argument is the name of an action, a string"}.
}}.

(* [elpi point_run_path "Name" Sel ...] prints the line of the action Name
   for selections given by paths instead of ranges: a selection is "P", the
   subterm at path P of the conclusion, or "H" "P", the one of the type of
   the hypothesis H.  A path is written "i.j.k" ("" for the whole part), in
   the immediate subterms of pbp_select.v (kids), the paths that Rocq's
   Set Printing Subterm Paths puts on the printed subterms (Pp tags
   "path:i.j.k").  The part is not printed again.  A subterm that cannot
   be selected (the return type of a match, a binder of a branch, the type
   of a binder that the rest depends on, a term under a coercion that is
   not printed: its pattern does not pass the check) is widened to the
   nearest subterm above it that can and is printed as a whole, with a
   warning (pbp-widened) as for point_run, unless it prints as the
   selection (a coercion).  The goal is unchanged. *)
Elpi Tactic point_run_path.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  (tool-name "point_run_path" => (
     point-run-paths Ctx Ty Args Line Ws,
     msg "the selection is widened to" M)),
  std.forall Ws (w\ coq.warning "pbp" "pbp-widened" M w),
  coq.say Line.
}}.

(* [elpi point_run_path_expect "Name" Line Ws Sel ...], for the tests: fails
   unless point_run_path gives the line Line, with the widened subterms Ws
   (separated by " / ", "" for none) *)
Elpi Tactic point_run_path_expect.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ [str Name, str Exp, str ExpW | Args] as G) [seal G] :-
  (tool-name "point_run_path" => point-run-paths Ctx Ty [str Name | Args] Line Ws),
  std.string.concat " / " Ws W,
  ((Line = Exp, W = ExpW), ! ;
   coq.ltac.fail 0 "point_run_path_expect: got" Line W "expected" Exp ExpW).
}}.

(* ---------------- The round trip of the paths ----------------
   For point_paths_roundtrip.sh: the subterm of a goal at a path that the
   printer tags (Set Printing Subterm Paths) must print as the tagged text. *)

Elpi Accumulate pbp_select.db lp:{{

% [rt-norm S N] N is the text S without blanks, without the parentheses
% around it and without a scope delimiter at its end (%Z): the two texts
% compared are printed alone and inside the goal
pred rt-norm i:string, o:string.
rt-norm S N :- flat S F0, rex.replace "let'" "let" F0 F1, rex.replace "^@" "" F1 F,
  rt-strip F N.
pred rt-strip i:string, o:string.
rt-strip S N :- rex.match "^.*%[A-Za-z_][A-Za-z_0-9]*$" S, not (rex.match "^\".*\"$" S),
  rex.replace "%[A-Za-z_][A-Za-z_0-9]*$" "" S S1, !, rt-strip S1 N.
rt-strip S N :- starts-with "(" S, ends-with ")" S, L is size S - 2, L > 0,
  S1 is substring S 1 L, rt-balanced S1, !, rt-strip S1 N.
rt-strip S S.

% [rt-balanced S] the parentheses of S are balanced
pred rt-balanced i:string.
rt-balanced S :- rex.split "" S Cs, std.fold Cs 0 (c\ a\ b\
    (c = "(", !, b is a + 1 ; c = ")", !, a > 0, b is a - 1 ; b = a)) 0.

% [rt-text Names M T P S] S is the text, at path P of the part T, that a
% tag of the printer covers: the subterm, or the name of a binder
pred rt-text i:list string, i:bmode, i:term, i:list int, o:string.
rt-text Names M T P S :- name-at T P _, !, rt-name-at Names [] M T P S.
rt-text Names M T P S :- path-of T P, !, text-at-names Names M P T S.

% [rt-name-at Ctx Sc M T P S] S is the name, as the display prints it, of
% the binder at P of T (P ends at its name); Ctx: the hypotheses, Sc: the
% names of the binders above, M: where T is (the conclusion: a name in
% Ctx or Sc is changed, x0; a hypothesis: only when the hypothesis of
% that name is used below); an unused variable is printed _ (in a
% pattern)
% [rt-in-context T P NE Off] the subterm at path P of T, printed inside T
% (shown-at), is the text NE (normalized: rt-norm) and starts after Off
% characters that are not blanks
% [rt-context-elsewhere T P NE Off] the subterm at P is found in the
% printing of T (shown-at), but not with the text NE after Off characters
pred rt-context-elsewhere i:term, i:list int, i:string, i:int.
rt-context-elsewhere T P NE Off :- not (name-at T P _), path-of T P,
  coq.term->string T S, flat S O, marker-names O A B,
  shown-at T O A B P _, not (rt-in-context T P NE Off).

pred rt-in-context i:term, i:list int, i:string, i:int.
rt-in-context T P NE Off :- not (name-at T P _), path-of T P,
  coq.term->string T S, flat S O, marker-names O A B,
  shown-at T O A B P (shown _ St _ Txt), rt-norm Txt NE,
  % (the parentheses around the subterm may be in its tag or not)
  (St = Off ; St is Off + 1 ; St is Off - 1), !.

pred rt-name-at i:list string, i:list string, i:bmode, i:term, i:list int, o:string.
rt-name-at Ctx Sc M T [0] S :- rt-binder T N F, !, rt-display Ctx Sc M N F tt S.
rt-name-at Ctx Sc M T [I|P] S :- kids T Ks, std.nth I Ks K, kid-mode M T I M1,
  (K = kt V, rt-name-at Ctx Sc M1 V P S ;
   K = kb N _ F, rt-display Ctx Sc M N F ff D,
   pi x\ rt-name-at Ctx [D|Sc] M1 (F x) P S).

pred rt-binder i:term, o:name, o:(term -> term).
rt-binder (prod N _ F) N F.
rt-binder (fun N _ F) N F.
rt-binder (let N _ _ F) N F.

% [rt-display Ctx Sc M N F U S] S is the name printed for the binder N of
% body F (U: an unused variable is printed _)
pred rt-display i:list string, i:list string, i:bmode, i:name, i:(term -> term), i:bool, o:string.
rt-display _ _ _ _ F tt "_" :- not (pi x\ occurs x (F x)), !.
rt-display Ctx Sc M N F _ S :- coq.name->id N S0, std.append Ctx Sc Avoid,
  (M = bm-goal _, std.mem! Avoid S0, !, fresh-ident S0 Avoid S ;
   std.mem! Ctx S0, (pi x\ var-named-in S0 (F x)), !, fresh-ident S0 Avoid S ;
   S = S0).
}}.

(* [elpi point_path_text Case "P" "Text"] or [... Case "H" "P" "Text"]:
   prints RT-OK, or RT-MISMATCH with what is at the path, when the subterm
   (or binder name) at path P of the conclusion (of the type of H) does not
   print as Text (blanks, outer parentheses and a final %scope ignored) *)
Elpi Tactic point_path_text.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
pred rt-part i:goal-ctx, i:term, i:list argument, o:term, o:bmode, o:string, o:string, o:string.
rt-part _ Ty [str P, str E, str _] Ty (bm-goal 0) "|-" P E :- is-path-string P, !.
rt-part Ctx _ [str H, str P, str E, str _] T bm-hyp H P E :-
  std.mem Ctx (decl _ N _), coq.name->id N H, !, hyp-of Ctx H _ T.
solve (goal Ctx _ Ty _ [str Case | Args] as G) [seal G] :-
  std.last Args (str OffS), Off is string_to_int OffS,
  (Args = [str H, str _, str _, str _], not (is-path-string H),
   not (std.mem Ctx (decl _ N0_ _), coq.name->id N0_ H), !,
   coq.say "RT-SKIP" Case H "(not a hypothesis of the goal for Rocq-Elpi: a section variable)" ;
  rt-part Ctx Ty Args T M Where P E,
  std.map-filter Ctx (d\ h\ sigma V N Ty1 B\ (d = decl V N Ty1 ; d = def V N Ty1 B),
                         coq.name->id N h) Names,
  path-of-string P Q,
  (rt-text Names M T Q S, ! ; S = "(no subterm)"),
  rt-norm S NS, rt-norm E NE,
  (NS = NE, rt-context-elsewhere T Q NE Off, !, coq.say "RT-OK-TEXT" Case Where P "(the same text, but in context it is printed elsewhere)" ;
   NS = NE, !, coq.say "RT-OK" Case Where P ;
   % the decider: the subterm at the path printed in its context (the whole
   % part printed with it framed by two markers, as pbp_select's shown-at
   % does) is the tagged text, at the same place (the number of characters
   % before it, blanks not counted)
   rt-in-context T Q NE Off, !, coq.say "RT-OK-CONTEXT" Case Where P ;
   % a let or a let '(..) := .. (a match) that Rocq-Elpi prints in another
   % style (let (x, _) := s, nested lets, (t : T) for let k := t in k)
   rex.match "^.*let[ ']" E, !, coq.say "RT-STYLE" Case Where P "tag:" E "path:" S ;
   coq.say "RT-MISMATCH" Case Where P "tag:" E "path:" S)).

}}.

(* [elpi point_paths_check] (point_paths_cases.v): every subterm and binder
   name of the conclusion and of the hypotheses has a text (rt-text); it
   prints their number.  point_paths_roundtrip.sh replaces it by the round
   trip of the tags of the printer *)
Elpi Tactic point_paths_check.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
pred rt-names-paths i:term, o:list (list int).
rt-names-paths T Ps :- std.findall (rt-name-path T P_) Sols,
  std.map Sols (s\ p\ s = rt-name-path T p) Ps.
pred rt-name-path i:term, o:list int.
rt-name-path T P :- path-of T Q, binder-kind-at T Q, std.append Q [0] P.
pred binder-kind-at i:term, i:list int.
binder-kind-at T Q :- name-at T {std.append Q [0]} _.
pred rt-count i:list string, i:bmode, i:term, o:int.
rt-count Names M T N :-
  std.findall (path-of T P_) Sols, std.map Sols (s\ p\ s = path-of T p) Ps0,
  rt-names-paths T Ps1, std.append Ps0 Ps1 Ps,
  std.forall Ps (p\ sigma S\ rt-text Names M T p S), std.length Ps N.
solve (goal Ctx _ Ty _ [] as G) [seal G] :-
  std.map-filter Ctx (d\ h\ sigma V N Ty1\ d = decl V N Ty1, coq.name->id N h) Hs,
  std.map-filter Ctx (d\ h\ sigma V N Ty1 B\ (d = decl V N Ty1 ; d = def V N Ty1 B),
                         coq.name->id N h) Names,
  rt-count Names (bm-goal 0) Ty N0,
  std.map Hs (h\ n\ sigma V T\ hyp-of Ctx h V T, rt-count Names bm-hyp T n) Ns,
  std.fold Ns N0 (a\ b\ c\ c is a + b) N,
  coq.say "point_paths_check:" N "paths".
}}.

(* [elpi point_paths_untagged Case Part P1 .. Pn], for
   point_paths_roundtrip.sh: Part is "|-" (the conclusion) or a hypothesis,
   P1 .. Pn the paths the printer tagged in it; prints RT-UNTAGGED for each
   binder name of the part (of a binder whose variable is used) that no
   tag names: a name the display prints without its tag (exists x, ..) *)
Elpi Tactic point_paths_untagged.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
pred rt-used-name-path i:term, o:list int.
rt-used-name-path T P :- path-of T Q, std.append Q [0] P, name-at T P _,
  rt-binder-used T Q.
pred rt-binder-used i:term, i:list int.
rt-binder-used T [] :- !, rt-binder T _ F, pi x\ occurs x (F x).
rt-binder-used T [I|Q] :- kids T Ks, std.nth I Ks K,
  (K = kt U, rt-binder-used U Q ; K = kb _ _ F, pi x\ rt-binder-used (F x) Q).
solve (goal Ctx _ Ty _ [str Case, str Where | Tags] as G) [seal G] :-
  (Where = "|-", !, T = Ty, M = bm-goal 0 ;
   std.mem Ctx (decl _ N _), coq.name->id N Where, !, hyp-of Ctx Where _ T, M = bm-hyp ;
   T = {{ True }}, M = bm-hyp),
  std.map-filter Ctx (d\ h\ sigma V N1 Ty1 B\ (d = decl V N1 Ty1 ; d = def V N1 Ty1 B),
                         coq.name->id N1 h) Names,
  std.map Tags (t\ p\ sigma S\ t = str S, path-of-string S p) Ps,
  std.findall (rt-used-name-path T P_) Sols,
  std.forall Sols (s\ sigma P S PS PS0 R Q R1 Q1 B\ s = rt-used-name-path T P,
    ((std.mem! Ps P ;
      % (a binder that is not printed: no tag below it)
      std.rev P [_|R], std.rev R Q,
      not (std.exists Ps (t\ sigma Rest\ std.appendR Q [_|Rest] t))), ! ;
     (rt-name-at Names [] M T P S, ! ; S = "?"),
     std.map P (n\ x\ x is int_to_string n) PS0, std.string.concat "." PS0 PS,
     std.rev P [_|R1], std.rev R1 Q1, (text-at-names Names M Q1 T B, ! ; B = "?"),
     coq.say "RT-UNTAGGED" Case Where PS S "in" B)).
}}.
