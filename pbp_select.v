(* From a selection in the printed goal to the pattern of pbp.

   The interface of a proof by pointing shows the goal as Rocq prints it
   and lets one select a part of it; the tactic below turns the selection
   (a range of characters in the printed conclusion, or in the printed type
   of a hypothesis) into the pbp call to insert in the script:

     Goal a + b = b + a.        elpi pbp_pattern 0 1.
                                prints  pbp [X in X + _ = _].

   The ranges count the characters that are not blanks (spaces, tabs, line
   breaks), from 0, the end excluded, so that they do not depend on the
   width at which the goal is printed nor on its indentation; a character
   is a Unicode code point.

   Method.  A subterm of the goal is found in the printed goal by printing
   the goal again with that subterm s framed by two markers, [A s B], A
   and B two local variables whose names occur nowhere in the printed
   goal: an application of local variables prints alike under every
   printing option (Printing All, Implicit), and s stays, so that the
   binders above it are printed as before.  The text before A and the
   text after B are then the text before and after the subterm
   in the printed goal.  This is Rocq's own printer: notations, implicit
   arguments, coercions and parentheses are the ones of the goal, and two
   occurrences that print alike (the two [a] of [a + b = b + a]) are told
   apart by their places.  A subterm that is not printed as a whole (the
   function [Nat.add] behind [+], the implicit type of [=], [S O] inside
   the numeral [2]) has no range and cannot be selected.  The selected
   subterm is the smallest one whose range contains the selection.

   The pattern is the goal where the selected subterm becomes the variable
   of the pattern, applied to the variables bound above it that it uses,
   where the largest printed subterms beside the path to the selection
   become holes [_] (printed through a second marker, [pbp_hole]), and
   where the rest (the heads of applications, the parts not printed, the
   types of the dependent binders) is kept.  The pattern is then checked:
   its text is parsed and elaborated again, and it must be the goal once
   the variable is the selected subterm, at the selected place. *)

From Stdlib Require Import ssreflect.
From elpi Require Import elpi.
From coq_tmp Require Export pbp.

(* The marker of the holes of a pattern: it prints as its name only *)
Definition pbp_hole {A : Type} {a : A} : A := a.

Elpi Db pbp_select.db lp:{{

/* ---------------- Messages ---------------- */

% [tool-name T] the errors and warnings start with T, the name of the
% tactic that is run (point_run sets it for its own messages)
pred tool-name o:string.
tool-name "pbp_pattern".

% [msg S M] M is the message S, after the name of the tactic
pred msg i:string, o:string.
msg S M :- tool-name T, !, M is T ^ ": " ^ S.

/* ---------------- Strings ---------------- */

% [flat S F] F is S without its blanks
pred flat i:string, o:string.
flat S F :- rex.replace "[ \t\n\r]+" "" S F0, unicode-blanks Bs, std.fold Bs F0 (b\ s\ r\ rex.replace b "" s r) F.

% the blanks of JavaScript's \s that are not ASCII (the panels count with
% it): no-break spaces, the spaces U+2000-U+200A, line and paragraph
% separators, U+1680, U+205F, U+3000, the byte order mark; and \v, \f
pred unicode-blanks o:list string.
unicode-blanks [" ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", " ", "　", "﻿", "", ""].

% [one-line S L] L is S on one line: each run of blanks is one space
pred one-line i:string, o:string.
one-line S L :- rex.replace "[ \t\n\r]+" " " S L.

% [cp-length S N] N is the number of Unicode characters of the UTF-8
% string S (its bytes that do not continue a character)
pred cp-length i:string, o:int.
cp-length S N :-
  Cont is "[" ^ chr 128 ^ "-" ^ chr 191 ^ "]",
  rex.replace Cont "" S S1, N is size S1.

% [starts-with P S] S starts with P
pred starts-with i:string, i:string.
starts-with P S :-
  N is size P, M is size S, N =< M, P1 is substring S 0 N, P1 = P.

% [ends-with Q S] S ends with Q
pred ends-with i:string, i:string.
ends-with Q S :-
  N is size Q, M is size S, N =< M, Q1 is substring S (M - N) N, Q1 = Q.

% [between O P Q T] T is the text of O between its prefix P and its
% suffix Q (non empty)
pred between i:string, i:string, i:string, o:string.
between O P Q T :-
  starts-with P O, ends-with Q O, N is size O - size P - size Q, N > 0,
  T is substring O (size P) N.

% [identifiers S L] L are the words of S that may be identifiers
pred identifiers i:string, o:list string.
identifiers S L :- rex.split "[^A-Za-z0-9_']+" S L.

/* ---------------- Subterms and paths ----------------
   A path is the list of the positions of the immediate subterms to go
   through, from the root: in an application (app [F|Args]) the head is 0
   and the arguments 1, 2, ...; in a product or an abstraction the type of
   the binder is 0 and the body 1; in a let the type is 0, the value 1 and
   the body 2; in a match the matched term is 0, the return type 1 and the
   branches 2, 3, ... */

kind kid type.
type kt term -> kid.                           % an immediate subterm
type kb name -> term -> (term -> term) -> kid. % one under a binder: its
                                               % name, its type, the body

% [kids T Ks] Ks are the immediate subterms of T
pred kids i:term, o:list kid.
kids (app L) Ks :- !, std.map L (t\ k\ k = kt t) Ks.
kids (prod N T F) [kt T, kb N T F] :- !.
kids (fun N T F) [kt T, kb N T F] :- !.
kids (let N T B F) [kt T, kt B, kb N T F] :- !.
kids (match T R Bs) [kt T, kt R | Ks] :- !,
  std.map Bs (t\ k\ k = kt t) Ks.
kids _ [].

% [rebuild T Ks T1] T1 is T with the immediate subterms Ks
pred rebuild i:term, i:list kid, o:term.
rebuild (app _) Ks T :- !,
  std.map Ks (k\ t\ k = kt t) [H|Args], mk-app H Args T.
rebuild (prod N _ _) [kt T, kb _ _ F] (prod N T F) :- !.
rebuild (fun N _ _) [kt T, kb _ _ F] (fun N T F) :- !.
rebuild (let N _ _ _) [kt T, kt B, kb _ _ F] (let N T B F) :- !.
rebuild (match _ _ _) [kt T, kt R | Ks] (match T R Bs) :- !,
  std.map Ks (k\ t\ k = kt t) Bs.
rebuild T [] T.

% [mk-app H Args T] T is H applied to Args, as one application; unlike
% coq.mk-app, a head fun or let is not reduced ((fun x => x + y) a stays)
pred mk-app i:term, i:list term, o:term.
mk-app H [] H :- !.
mk-app (app L) Args (app L1) :- !, std.append L Args L1.
mk-app H Args (app [H|Args]).

% [map-kid Bs F K K1] K1 is the subterm K changed by F, which is given the
% variables bound above it (Bs, the outermost first)
pred map-kid i:list term, i:(pred i:list term, i:term, o:term),
             i:kid, o:kid.
map-kid Bs F (kt T) (kt T1) :- F Bs T T1.
map-kid Bs F (kb N Ty B) (kb N Ty B1) :-
  pi x\ decl x N Ty =>
    sigma Bs1\ (std.append Bs [x] Bs1, F Bs1 (B x) (B1 x)).

% [path-of T P] P is the path of a subterm of T (all of them, the root
% first, on backtracking)
pred path-of i:term, o:list int.
path-of _ [].
path-of T [I|P] :-
  kids T Ks, std.length Ks N, N > 0, std.iota N Is, std.mem Is I,
  std.nth I Ks K, kid-path K P.

% [kid-path K P] P is the path of a subterm of the subterm K
pred kid-path i:kid, o:list int.
kid-path (kt T) P :- path-of T P.
kid-path (kb _ _ B) P :- pi x\ path-of (B x) P.

% [replace-at P Bs F T T1] T1 is T where its subterm S at path P is
% replaced by R, with F Bs' S R, Bs' being Bs and the variables bound above S
pred replace-at i:list int, i:list term,
                i:(pred i:list term, i:term, o:term), i:term, o:term.
replace-at [] Bs F T R :- !, F Bs T R.
replace-at [I|P] Bs F T T1 :-
  kids T Ks, std.split-at I Ks Before [K|After],
  map-kid Bs (bs\ t\ r\ replace-at P bs F t r) K K1,
  std.append Before [K1|After] Ks1, rebuild T Ks1 T1.

% [on-path P Ps] P is a prefix of one of the paths Ps
pred on-path i:list int, i:list (list int).
on-path P Ps :- std.exists Ps (q\ std.appendR P _ q).

/* ---------------- The printed subterms ---------------- */

kind shown type.
% [shown P S E T] the subterm at path P is printed from the character S
% (included) to E (excluded), and its text without blanks is T
type shown list int -> int -> int -> string -> shown.

% [marker-names O A B] A and B, the names of the two markers, are names
% that do not occur in O, the printed term (without blanks): so the
% printer neither renames a binder of the term nor mixes them with its text
pred marker-names i:string, o:string, o:string.
marker-names O A B :- marker-fresh O "pbp_mark" 0 A, marker-fresh O "pbp_end" 0 B.

pred marker-fresh i:string, i:string, i:int, o:string.
marker-fresh O Base 0 Name :- not (contains O Base), !, Name = Base.
marker-fresh O Base N Name :- N > 0, std.any->string N NS, C is Base ^ NS,
  not (contains O C), !, Name = C.
marker-fresh O Base N Name :- N1 is N + 1, marker-fresh O Base N1 Name.

% [contains S T] the string T occurs in S
pred contains i:string, i:string.
contains S T :- rex.match {calc (".*" ^ T ^ ".*")} S.

% [marked-string A B P T S] S is the printing (without blanks) of T where
% the subterm s at path P is replaced by A s B, A and B two local variables
% (an application of local variables prints alike under every printing
% option, Printing All included; s stays, so that the binders above it
% print as in T)
pred marked-string i:string, i:string, i:list int, i:term, o:string.
marked-string A B P T S :-
  coq.id->name A NA, coq.id->name B NB,
  (pi a b\ decl a NA {{ Prop }} => decl b NB {{ Prop }} =>
     sigma M\ (replace-at P [] (_\ s\ r\ r = app [a, s, b]) T M,
      coq.term->string M MS)),
  flat MS S.

% [around-mark A B M P Q] the text M (without blanks) is P, then the
% marker A, the subterm, the marker B, then Q (fails when the markers are
% not printed: the subterm is not, an implicit argument say)
pred around-mark i:string, i:string, i:string, o:string, o:string.
around-mark A B M P Q :-
  contains M A, contains M B,
  rex.replace {calc (A ^ ".*")} "" M P, rex.replace {calc (".*" ^ B)} "" M Q.

% [fits O P Q B T] T is the text of O between P and Q, B being the text
% before it: first P and Q without the parentheses around the markers (the
% application A s B is printed in parentheses where s may be printed with
% or without its own: then T is s with its own, as in O), else P and Q
pred fits i:string, i:string, i:string, o:string, o:string.
fits O P Q P1 T :-
  ends-with "(" P, starts-with ")" Q,
  P1 is substring P 0 (size P - 1), Q1 is substring Q 1 (size Q - 1),
  between O P1 Q1 T, !.
fits O P Q P T :- between O P Q T.

% [shown-at T O A B P Sh] the subterm of T at path P is printed as a whole in
% O, the printing of T without blanks, as Sh says (A, B: the markers)
pred shown-at i:term, i:string, i:string, i:string, i:list int, o:shown.
shown-at T O A B P (shown P S E Txt) :-
  marked-string A B P T MF,
  around-mark A B MF Pre Post, fits O Pre Post Before Txt,
  cp-length Before S, cp-length Txt L, E is S + L.

% [shown-all T Shs] Shs are the subterms of T printed as a whole, and
% where they are in the printing of T
pred shown-all i:term, o:list shown.
shown-all T Shs :-
  coq.term->string T S, flat S O, marker-names O A B,
  std.findall (path-of T P_) Sols,
  std.map-filter Sols (s\ sh\ sigma P\ s = path-of T P,
                          not (not-printed T P), shown-at T O A B P sh)
    Shs.

% [not-printed T P] the subterm at path P of T is never printed as a
% subterm, and marking it breaks the printing of the match it is in: the
% return type of a match (or a subterm of it), or a branch of a match that
% binds the arguments of its constructor (its fun ..., and the fun ... of
% the next arguments: the binders of the pattern S k)
pred not-printed i:term, i:list int.
not-printed (match _ _ _) [1|_] :- !.
not-printed (match _ _ Bs) [I|P] :- I >= 2, J is I - 2, std.nth J Bs Br,
  branch-binder P Br, !.
not-printed T [I|P] :- kids T Ks, std.nth I Ks K, kid-not-printed P K.

pred kid-not-printed i:list int, i:kid.
kid-not-printed P (kt T) :- not-printed T P.
kid-not-printed P (kb _ _ B) :- pi x\ not-printed (B x) P.

% [branch-binder P Br] the path P of the branch Br ends at one of its
% leading fun (its body is the kid 1 of a fun)
pred branch-binder i:list int, i:term.
branch-binder [] (fun _ _ _).
branch-binder [1|P] (fun _ _ F) :- pi x\ branch-binder P (F x).

% [text-at P T S] S is the subterm of T at path P, printed on one line
pred text-at i:list int, i:term, o:string.
text-at [] T S :- coq.term->string T S0, one-line S0 S.
text-at [I|P] T S :- kids T Ks, std.nth I Ks K, kid-text P K S.

% [kid-text P K S] S is the subterm at path P of the subterm K
pred kid-text i:list int, i:kid, o:string.
kid-text P (kt T) S :- text-at P T S.
kid-text P (kb N Ty B) S :- pi x\ decl x N Ty => text-at P (B x) S.

/* ---------------- From a range to a subterm ---------------- */

% [better A B C] C is the better of the subterms A and B for a selection
% that both contain: the shorter, then the less deep, then A
pred better i:shown, i:shown, o:shown.
better (shown P S E T) (shown P1 S1 E1 _) (shown P S E T) :-
  L is E - S, L1 is E1 - S1,
  (L < L1 ; L = L1, std.length P D, std.length P1 D1, D =< D1), !.
better _ B B.

% [smallest Shs S E Sh] Sh is the best printed subterm of Shs whose range
% contains the range [S, E)
pred smallest i:list shown, i:int, i:int, o:shown.
smallest Shs S E Sh :-
  std.filter Shs (sh\ sigma S1 E1\ sh = shown _ S1 E1 _, S1 =< S, E =< E1)
    [C|Cs],
  std.fold Cs C better Sh.

% [exact Sh S E] the range [S, E) is the subterm Sh, with or without its
% parentheses
pred exact i:shown, i:int, i:int.
exact (shown _ S E _) S E :- !.
exact (shown _ S0 E0 T) S E :-
  starts-with "(" T, ends-with ")" T, S is S0 + 1, E is E0 - 1.

/* ---------------- Selections ---------------- */

kind sel type.
type sel-goal int -> int -> sel.          % a range in the conclusion
type sel-hyp string -> int -> int -> sel. % a range in the type of a
                                          % hypothesis

% [parse-sels As Sels] the arguments As are the selections Sels
pred parse-sels i:list argument, o:list sel.
parse-sels [] [] :- !.
parse-sels [int S, int E | As] [sel-goal S E | Sels] :- !,
  parse-sels As Sels.
parse-sels [str H, int S, int E | As] [sel-hyp H S E | Sels] :- !,
  parse-sels As Sels.
parse-sels _ _ :-
  coq.ltac.fail 0 {msg "a selection is S E (a range in the conclusion) or H S E (a range in the hypothesis H)"}.

% [hyp-of Ctx H V T] H is the name of the hypothesis V of type T in Ctx
% (not a local definition)
pred hyp-of i:goal-ctx, i:string, o:term, o:term.
hyp-of Ctx H V T :- std.mem Ctx (decl V N T), coq.name->id N H, !.
hyp-of Ctx H _ _ :- std.mem Ctx (def _ N _ _), coq.name->id N H, !,
  coq.ltac.fail 0 {msg "the hypothesis"} H "is a definition".
hyp-of _ H _ _ :- coq.ltac.fail 0 {msg "no hypothesis"} H.

% [sel-hyps Ctx Sels Hs] Hs are the hypotheses of the selections Sels, in
% the order of the context (the oldest first)
pred sel-hyps i:goal-ctx, i:list sel, o:list string.
sel-hyps Ctx Sels Hs :-
  std.map-filter Ctx (d\ h\ sigma V N T B\ (d = decl V N T ; d = def V N T B),
                         coq.name->id N h,
                         std.exists Sels (s\ sigma S E\ s = sel-hyp h S E))
    Hs0,
  % the context of a goal lists its youngest hypothesis first
  std.rev Hs0 Hs.

% [ones N L] L is the list of N ones
pred ones i:int, o:list int.
ones 0 [] :- !.
ones N [1|L] :- N1 is N - 1, ones N1 L.

% [revert Ctx Hs G C] C is G with the hypotheses Hs generalized (as
% move: Hs does): forall H1 .. Hn, G
pred revert i:goal-ctx, i:list string, i:term, o:term.
revert _ [] G G.
revert Ctx [H|Hs] G (prod N T F) :-
  hyp-of Ctx H V T, coq.id->name H N, revert Ctx Hs G C,
  pi x\ (copy V x :- !) => copy C (F x).

kind part type.
% [part B T Shs] a part of the generalized goal: the hypothesis or the
% conclusion T at path B, its subterms printed as Shs (paths from T)
type part list int -> term -> list shown -> part.

% [parts Ctx Hs G Ps] Ps are the parts of the goal G with the hypotheses
% Hs generalized: the hypotheses, then the conclusion
pred parts i:goal-ctx, i:list string, i:term, o:list part.
parts Ctx Hs G Ps :-
  std.map-i Hs (i\ h\ p\ sigma B0 B V T Shs\ ones i B0, std.append B0 [0] B,
                        hyp-of Ctx h V T, shown-all T Shs, p = part B T Shs)
    PHs,
  std.length Hs N, ones N BG, shown-all G ShG,
  std.append PHs [part BG G ShG] Ps.

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
locate _ Hs Ps (sel-goal S E) (loc P N P0) W :- !,
  std.length Hs N, std.nth N Ps Part, locate-in Part S E P P0 W.
locate _ Hs Ps (sel-hyp H S E) (loc P I P0) W :-
  std.length Hs N, std.iota N Is,
  std.mem Is I, std.nth I Hs H, !, std.nth I Ps Part,
  locate-in Part S E P P0 W.
% (no hypothesis H: hyp-of fails with the error)
locate Ctx _ _ (sel-hyp H _ _) _ _ :- hyp-of Ctx H _ _, !, fail.

% [locate-in Part S E P P0 W] the range [S, E) of the part Part is its
% subterm at path P0, at path P of the generalized goal, W as in locate
pred locate-in i:part, i:int, i:int, o:list int, o:list int, o:string.
locate-in _ S E _ _ _ :- E < S, !,
  coq.ltac.fail 0 {msg "the range"} S E "ends before it starts".
locate-in (part B T Shs) S E P P0 W :-
  (E = S, E1 is S + 1 ; E > S, E1 = E), !,
  (smallest Shs S E1 Sh ;
   coq.ltac.fail 0 {msg "the range"} S E "is not in the printed term"),
  !, Sh = shown P0 _ _ _,
  ((E = S ; exact Sh S E), !, W = "" ; text-at P0 T W),
  std.append B P0 P.

/* ---------------- The pattern ---------------- */

% [kept T I] the I-th immediate subterm of T stays as it is in the
% pattern, when it holds no selection: the head of an application, the
% type of a dependent binder or of a let, the return type of a match, the
% body of a cast (Rocq-Elpi sees the cast (t : T) as let _ : T := t in _
% whose body is the bound variable: so it prints back as a cast)
pred kept i:term, i:int.
kept (app _) 0.
kept (prod _ _ F) 0 :- pi x\ occurs x (F x).
kept (fun _ _ F) 0 :- pi x\ occurs x (F x).
kept (let _ _ _ _) 0.
kept (let _ _ _ F) 2 :- pi x\ F x == x.
kept (match _ _ _) 1.

% [hole T H] H is the hole that prints as _ in place of T; it keeps T (and
% its type, not a new evar), for the binders above it to print as before
pred hole i:term, o:term.
hole T {{ @pbp_hole lp:Ty lp:T }} :- coq.typecheck T Ty ok, !.
hole T {{ @pbp_hole Prop lp:T }}.

% [pattern Sels Vis P Bs T R] R is the pattern of the subterm T at path
% P, Bs being the variables bound above it: Sels maps the selected paths
% to the variables of the pattern, Vis are the paths of the printed
% subterms (the holes)
pred pattern i:list (pair (list int) term), i:list (list int), i:list int,
             i:list term, i:term, o:term.
pattern Sels _ P Bs T R :- std.lookup Sels P X, !,
  std.filter Bs (v\ occurs v T) Vs, coq.mk-app X Vs R0, annotated T R0 R.
pattern Sels Vis P _ T H :-
  std.map Sels fst Ps, not (on-path P Ps), std.mem! Vis P, !, hole T H.
pattern Sels Vis P Bs T R :-
  kids T Ks, std.map-i Ks (pattern-kid Sels Vis P Bs T) Ks1,
  rebuild T Ks1 R.

% [pattern-kid Sels Vis P Bs T I K K1] K1 is the pattern of K, the I-th
% immediate subterm of T (at path P)
pred pattern-kid i:list (pair (list int) term), i:list (list int),
                 i:list int, i:list term, i:term, i:int, i:kid, o:kid.
pattern-kid Sels _ P _ T I K K :-
  std.append P [I] PI, std.map Sels fst Ps, not (on-path PI Ps),
  kept T I, !.
pattern-kid Sels Vis P Bs _ I K K1 :-
  std.append P [I] PI, map-kid Bs (bs\ t\ r\ pattern Sels Vis PI bs t r) K K1.

% [default-printing G] G, run with the printing options at their default
% (Printing All, Implicit, Coercions unset, Notations set), then put back:
% the pattern is a line of the script, whatever the goal display uses
pred default-printing i:prop.
default-printing G :-
  Off = [["Printing", "All"], ["Printing", "Implicit"], ["Printing", "Coercions"]],
  On = ["Printing", "Notations"],
  std.map Off (o\ v\ coq.option.get o v) OldOff, coq.option.get On OldOn,
  std.forall Off (o\ coq.option.set o (coq.option.bool ff)),
  coq.option.set On (coq.option.bool tt),
  (G, !, R = tt ; R = ff),
  std.forall2 Off OldOff (o\ v\ coq.option.set o v), coq.option.set On OldOn,
  R = tt.

% [pattern-text Ns Ctx M Ps C Vis Xs T] T is the text of the pattern of C,
% the selections at paths Ps being the variables named Ns (Xs: those
% already bound); Ctx are the names of the hypotheses of the goal and M
% says where C is (the names of its binders: display-names)
pred pattern-text i:list string, i:list string, i:bmode, i:list (list int),
                  i:term, i:list (list int), i:list term, o:string.
pattern-text [N|Ns] Ctx M Ps C Vis Xs T :-
  coq.id->name N Nm,
  pi x\ decl x Nm {{ Prop }} =>
    sigma Xs1\ (std.append Xs [x] Xs1, pattern-text Ns Ctx M Ps C Vis Xs1 T).
pattern-text [] Ctx M Ps C Vis Xs T :-
  std.map2 Ps Xs (p\ x\ s\ s = pr p x) Sels,
  pattern Sels Vis [] [] C P,
  display-names Ctx [] M P P1 [] Rs,
  default-printing (coq.term->string P1 S),
  rex.replace "pbp_hole" "_" S S1, replace-placeholders Rs S1 S2,
  one-line S2 T.

/* The names of the binders of a pattern.  Rocq-Elpi prints a binder whose
   name is the name of a hypothesis of the goal under a name of its own
   (elpi_ctx_entry_3_), where the goal display (Rocq's) names it as Rocq
   does: in the conclusion, with a new name (x0, Rocq avoids the names of
   the hypotheses there); in the type of a hypothesis, with its own name,
   unless the hypothesis of that name occurs under it (then a new name).
   Such a binder is printed under a placeholder name, which is then
   replaced by that name. */

kind bmode type.
type bm-goal int -> bmode. % the goal with N hypotheses generalized in front
                           % (forall H1 .. HN, conclusion)
type bm-hyp bmode.         % the type of a hypothesis

% [display-names Ctx Sc M T T1 R0 R] T1 is T where the binders that
% Rocq-Elpi would rename (named as one of the hypotheses Ctx) have a
% placeholder name; R is R0 with the pairs (placeholder, name to print); Sc
% are the names of the binders above T, M says where T is
pred display-names i:list string, i:list string, i:bmode, i:term, o:term,
                   i:list (pair string string), o:list (pair string string).
display-names Ctx Sc (bm-goal K) (prod N Ty F) (prod N1 Ty1 F1) R0 R :- K > 0, !,
  K1 is K - 1,
  display-names Ctx Sc bm-hyp Ty Ty1 R0 R1,
  display-binder Ctx Sc bm-hyp N F N1 Sc1 R1 R2,
  pi x\ display-names Ctx Sc1 (bm-goal K1) (F x) (F1 x) R2 R.
display-names Ctx Sc M (prod N Ty F) (prod N1 Ty1 F1) R0 R :- !,
  display-names Ctx Sc M Ty Ty1 R0 R1,
  display-binder Ctx Sc M N F N1 Sc1 R1 R2,
  pi x\ display-names Ctx Sc1 M (F x) (F1 x) R2 R.
display-names Ctx Sc M (fun N Ty F) (fun N1 Ty1 F1) R0 R :- !,
  display-names Ctx Sc M Ty Ty1 R0 R1,
  display-binder Ctx Sc M N F N1 Sc1 R1 R2,
  pi x\ display-names Ctx Sc1 M (F x) (F1 x) R2 R.
display-names Ctx Sc M (let N Ty B F) (let N1 Ty1 B1 F1) R0 R :- !,
  display-names Ctx Sc M Ty Ty1 R0 R1,
  display-names Ctx Sc M B B1 R1 R2,
  display-binder Ctx Sc M N F N1 Sc1 R2 R3,
  pi x\ display-names Ctx Sc1 M (F x) (F1 x) R3 R.
display-names Ctx Sc M T T1 R0 R :-
  kids T Ks, std.fold-map Ks R0 (k\ r\ k1\ r1\ sigma U U1\ k = kt U,
                     display-names Ctx Sc M U U1 r r1, k1 = kt U1) Ks1 R,
  rebuild T Ks1 T1.

% [display-binder Ctx Sc M N F N1 Sc1 R0 R] N1 is the name to give the
% binder N of body F (its placeholder, or N), Sc1 is Sc with the name it
% is printed with
pred display-binder i:list string, i:list string, i:bmode, i:name,
                    i:(term -> term), o:name, o:list string,
                    i:list (pair string string), o:list (pair string string).
display-binder Ctx Sc M N F N1 [D|Sc] R0 [pr Ph D|R0] :-
  coq.name->id N S, std.mem! Ctx S, !,
  std.append Ctx Sc Avoid,
  (M = bm-goal _, !, fresh-ident S Avoid D ;
   (pi x\ var-named-in S (F x)), !, fresh-ident S Avoid D ;
   D = S),
  std.length R0 K, Ph is "pbpbinder" ^ int_to_string K ^ "x",
  coq.id->name Ph N1.
display-binder _ Sc _ N _ N [S|Sc] R R :- coq.name->id N S.

% [var-named-in S T] a variable of the context named S occurs in T
pred var-named-in i:string, i:term.
var-named-in S T :- name T, !, (decl T N _ ; def T N _ _), coq.name->id N S.
var-named-in S T :- kids T Ks, std.exists Ks (kid-var-named-in S).

pred kid-var-named-in i:string, i:kid.
kid-var-named-in S (kt T) :- var-named-in S T.
kid-var-named-in S (kb _ _ B) :- pi x\ var-named-in S (B x).

% [fresh-ident S Avoid D] D is the name Rocq gives in place of S to avoid
% the names Avoid: S, else S with a number (from 0, or after the number
% that S ends with)
pred fresh-ident i:string, i:list string, o:string.
fresh-ident S Avoid S :- not (std.mem! Avoid S), !.
fresh-ident S Avoid D :-
  (rex.match "^.*[^0-9][0-9]+$" S, !,
   rex.replace "[0-9]+$" "" S Base, rex.replace "^.*[^0-9]" "" S NS,
   I is string_to_int NS + 1 ;
   Base = S, I = 0),
  fresh-ident-from Base I Avoid D.

pred fresh-ident-from i:string, i:int, i:list string, o:string.
fresh-ident-from Base I Avoid D :-
  D1 is Base ^ int_to_string I, not (std.mem! Avoid D1), !, D = D1.
fresh-ident-from Base I Avoid D :- I1 is I + 1, fresh-ident-from Base I1 Avoid D.

% [replace-placeholders Rs S S1] S1 is the text S where the placeholders
% of display-names are replaced by their names (Rs)
pred replace-placeholders i:list (pair string string), i:string, o:string.
replace-placeholders Rs S S1 :-
  std.fold Rs S (r\ s\ s1\ sigma Ph D\ r = pr Ph D, rex.replace Ph D s s1) S1.

% [text-at-names Ctx M P T S] S is the subterm of T at path P, printed on
% one line, as text-at does, but with the names of the binders of the goal
% display (display-names: Ctx, M)
pred text-at-names i:list string, i:bmode, i:list int, i:term, o:string.
text-at-names Ctx M [] T S :- !,
  display-names Ctx [] M T T1 [] Rs, coq.term->string T1 S0,
  replace-placeholders Rs S0 S1, one-line S1 S.
text-at-names Ctx M [I|P] T S :-
  kids T Ks, std.nth I Ks K, kid-mode M T I M1, kid-text-names Ctx M1 P K S.

pred kid-text-names i:list string, i:bmode, i:list int, i:kid, o:string.
kid-text-names Ctx M P (kt T) S :- text-at-names Ctx M P T S.
kid-text-names Ctx M P (kb N Ty B) S :-
  coq.name->id N Id, pi x\ decl x N Ty => text-at-names [Id|Ctx] M P (B x) S.

% [kid-mode M T I M1] M1 says where the I-th immediate subterm of T is, M
% where T is (the type of a generalized hypothesis, the rest after it)
pred kid-mode i:bmode, i:term, i:int, o:bmode.
kid-mode (bm-goal K) (prod _ _ _) 0 bm-hyp :- K > 0, !.
kid-mode (bm-goal K) (prod _ _ _) 1 (bm-goal K1) :- K > 0, !, K1 is K - 1.
kid-mode M _ _ M.

% [check Text Ps C] the pattern Text, parsed and elaborated, is C once its
% variables are the subterms at the paths Ps, at these places
pred check i:string, i:list (list int), i:term.
check Text Ps C :-
  S is "(" ^ Text ^ ")",
  coq.parse.argument S ff "" A D,
  (D = ok, A = trm Pat, !,
   (check-open Pat Ps Ps [] C, ! ;
    coq.ltac.fail 0 {msg "the pattern does not give back the goal with the selection (a selected subterm that the rest of the goal depends on cannot be abstracted)"}) ;
   D = error M, !,
   coq.ltac.fail 0 {msg "the pattern"} Text "does not elaborate:" M ;
   coq.ltac.fail 0 {msg "the pattern"} Text "is not a term").

% [check-ok Text Ps C] check succeeds (no error: a failure)
pred check-ok i:string, i:list (list int), i:term.
check-ok Text Ps C :-
  S is "(" ^ Text ^ ")",
  coq.parse.argument S ff "" A D, D = ok, A = trm Pat,
  check-open Pat Ps Ps [] C.

% [check-open Pat Ps Ps1 Xs C] the body of the pattern Pat (whose first
% variables are Xs) is C with its variables at the paths Ps (Ps1 are the
% paths of the variables still to open)
pred check-open i:term, i:list (list int), i:list (list int), i:list term,
                i:term.
check-open (fun N T F) Ps [_|Ps1] Xs C :- !,
  pi x\ decl x N T =>
    sigma Xs1\ (std.append Xs [x] Xs1, check-open (F x) Ps Ps1 Xs1 C).
check-open Body Ps [] Xs C :-
  std.map2 Ps Xs (p\ x\ s\ s = pr p x) Sels,
  pattern Sels [] [] [] C C1,
  coq.unify-eq Body C1 ok, !.

/* ---------------- The selections, resolved ----------------
   What the actions of point_actions.v are given (and pbp_pattern uses) */

kind point-in type.
% [point-in Names Hs C Parts Ls] selections in a goal: Names are the
% names of its hypotheses, Hs the hypotheses the selections are in (generalized, in the order of the context), C the goal with
% Hs generalized, Parts its parts, Ls the selections (in the order given)
type point-in list string -> list string -> term -> list part -> list loc ->
              point-in.

% [point-resolve Ctx G Sels In Ws] the selections Sels of the goal G
% (context Ctx) are In; Ws are the texts of the subterms that selections
% were widened to
pred point-resolve i:goal-ctx, i:term, i:list sel, o:point-in,
                   o:list string.
point-resolve Ctx G Sels (point-in Names Hs C Parts Ls) Ws :-
  std.map-filter Ctx (d\ h\ sigma V N T B\ (d = decl V N T ; d = def V N T B),
                         coq.name->id N h) Names,
  sel-hyps Ctx Sels Hs, revert Ctx Hs G C, parts Ctx Hs G Parts,
  std.map Sels (s\ lw\ sigma L W\ locate Ctx Hs Parts s L W, lw = pr L W)
    LWs,
  std.map LWs fst Ls, std.map-filter LWs (lw\ w\ lw = pr _ w, not (w = "")) Ws,
  std.map Ls loc-path Ps,
  (nested Ps, !,
   coq.ltac.fail 0 {msg "the two selections are the same subterm or one is inside the other"} ; true).

/* ---------------- Selections given by paths ----------------
   An interface whose goal display tags each printed subterm with its path
   (Rocq's Set Printing Subterm Paths) sends the path of the selected
   subterm in its part instead of a range: no character is counted and the
   part is not printed again. */

kind psel type.
type psel-goal list int -> psel.          % a path in the conclusion
type psel-hyp string -> list int -> psel. % a path in the type of a hypothesis

% [path-of-string S P] S is the path P written "i.j.k" ("" for the root)
pred path-of-string i:string, o:list int.
path-of-string "" [] :- !.
path-of-string S P :-
  rex.split "\\." S Ss,
  std.map Ss (s\ n\ (rex.match "^[0-9]+$" s, !, n is string_to_int s ;
                     coq.ltac.fail 0 {msg "not a path:"} S)) P.

% [is-path-string S] S is written as a path ("" or starting with a digit)
pred is-path-string i:string.
is-path-string "" :- !.
is-path-string S :- rex.match "^[0-9]" S.

% [parse-psels As Sels] the arguments As are the selections Sels: "P" (a
% path in the conclusion) or "H" "P" (a path in the hypothesis H)
pred parse-psels i:list argument, o:list psel.
parse-psels [] [] :- !.
parse-psels [str P | As] [psel-goal Q | Sels] :- is-path-string P, !,
  path-of-string P Q, parse-psels As Sels.
parse-psels [str H, str P | As] [psel-hyp H Q | Sels] :- is-path-string P, !,
  path-of-string P Q, parse-psels As Sels.
parse-psels _ _ :-
  coq.ltac.fail 0 {msg "a selection is \"P\" (a path in the conclusion, \"i.j.k\", \"\" for the root) or \"H\" \"P\" (a path in the hypothesis H)"}.

% [psel-sel S S1] the hypothesis of the path selection S, as a range
% selection S1 (for sel-hyps)
pred psel-sel i:psel, o:sel.
psel-sel (psel-goal _) (sel-goal 0 0).
psel-sel (psel-hyp H _) (sel-hyp H 0 0).

% [all-shown T Shs] every subterm of T, as if printed as a whole (the
% paths only: no range, no text), but those not-printed excludes; the
% patterns may put a hole at any of them, the check of the pattern is what
% tells that it is right
pred all-shown i:term, o:list shown.
all-shown T Shs :-
  std.findall (path-of T P_) Sols,
  std.map-filter Sols (s\ sh\ sigma P\ s = path-of T P, not (not-printed T P),
                          sh = shown P 0 0 "") Shs.

% [path-parts Ctx Hs G Ps] the parts of the goal G with the hypotheses Hs
% generalized, as parts does, their subterms given by all-shown
pred path-parts i:goal-ctx, i:list string, i:term, o:list part.
path-parts Ctx Hs G Ps :-
  std.map-i Hs (i\ h\ p\ sigma B0 B V T Shs\ ones i B0, std.append B0 [0] B,
                        hyp-of Ctx h V T, all-shown T Shs, p = part B T Shs)
    PHs,
  std.length Hs N, ones N BG, all-shown G ShG,
  std.append PHs [part BG G ShG] Ps.

% [path-locate Ctx Hs Ps Sel L W] the path selection Sel is L; W is the
% text of the subterm if the selection had to be widened to it, ""
% otherwise (as locate)
pred path-locate i:goal-ctx, i:list string, i:list part, i:psel, o:loc,
                 o:string.
path-locate Ctx Hs Ps (psel-goal P0) (loc P N P1) W :- !,
  std.length Hs N, std.nth N Ps Part, path-locate-in Ctx (bm-goal 0) Part P0 P P1 W.
path-locate Ctx Hs Ps (psel-hyp H P0) (loc P I P1) W :-
  std.length Hs N, std.iota N Is, std.mem Is I, std.nth I Hs H, !,
  std.nth I Ps Part, path-locate-in Ctx bm-hyp Part P0 P P1 W.

% [path-locate-in Ctx M Part P0 P P1 W] the path P0 of the part Part selects
% its subterm at path P1, at path P of the generalized goal: P0 itself if
% it can be selected (path-selectable), else the nearest subterm above it
% that can (path-widen), whose text is then W ("" if it is printed as the
% subterm at P0 alone: under a coercion that is not printed)
pred path-locate-in i:goal-ctx, i:bmode, i:part, i:list int, o:list int,
                    o:list int, o:string.
path-locate-in Ctx M (part B T _) P0 P P1 W :-
  std.map P0 (n\ s\ s is int_to_string n) Ss, std.string.concat "." Ss S,
  (path-of T P0, ! ; coq.ltac.fail 0 {msg "no subterm at the path"} S),
  std.map-filter Ctx (d\ h\ sigma V N Ty Bo\ (d = decl V N Ty ; d = def V N Ty Bo),
                         coq.name->id N h) Names,
  (path-selectable Names T P0, !, P1 = P0, W = "" ;
   path-widen Names T P0 P1 Txt1, text-at P0 T W0, flat W0 Txt0,
   ((Txt0 = Txt1 ; Txt1 is "(" ^ Txt0 ^ ")"), !, W = "" ;
    text-at-names Names M P1 T W)),
  std.append B P1 P.

% [path-selectable Ctx T P] the subterm at path P of T can be selected: it
% is printed (not the return type of a match nor a binder of a branch) and
% its pattern, alone in T, is right (not a binder type that the rest
% depends on, not a term under a coercion that is not printed); Ctx are
% the names of the hypotheses
pred path-selectable i:list string, i:term, i:list int.
path-selectable Ctx T P :- not (not-printed T P), pattern-ok Ctx T P.

% [pattern-ok Ctx T P] the pattern of the subterm at path P of T, alone,
% passes check (a failure, not an error, otherwise)
pred pattern-ok i:list string, i:term, i:list int.
pattern-ok Ctx T P :-
  all-shown T Shs, std.map Shs (sh\ v\ sh = shown v _ _ _) Vis,
  coq.term->string T S, identifiers S Ids, std.append Ctx Ids Avoid,
  fresh-names ["X"] Avoid [X], pattern-checked [X] X Ctx bm-hyp [P] T Vis _.

% [path-widen Ctx T P0 P1 Txt] P1 is the nearest path above P0 that can be
% selected and is printed as a whole (shown-at: as the range of a
% selection would be widened by locate), the root at worst; Txt is its
% text in the printing of T, without blanks
pred path-widen i:list string, i:term, i:list int, o:list int, o:string.
path-widen Ctx T P0 P1 Txt :-
  coq.term->string T S, flat S O, marker-names O A B,
  std.rev P0 [_|R], std.rev R Q, path-widen-from Ctx T O A B Q P1 Txt.

pred path-widen-from i:list string, i:term, i:string, i:string, i:string,
                     i:list int, o:list int, o:string.
path-widen-from _ _ O _ _ [] [] O :- !.
path-widen-from Ctx T O A B Q Q Txt :-
  not (not-printed T Q), shown-at T O A B Q (shown _ _ _ Txt),
  pattern-ok Ctx T Q, !.
path-widen-from Ctx T O A B Q P1 Txt :-
  std.rev Q [_|R], std.rev R Q1, path-widen-from Ctx T O A B Q1 P1 Txt.

% [point-resolve-paths Ctx G Sels In Ws] the path selections Sels of the
% goal G (context Ctx) are In, the value point-resolve gives for ranges;
% Ws are the texts of the subterms that selections were widened to
pred point-resolve-paths i:goal-ctx, i:term, i:list psel, o:point-in,
                         o:list string.
point-resolve-paths Ctx G Sels (point-in Names Hs C Parts Ls) Ws :-
  std.map-filter Ctx (d\ h\ sigma V N T B\ (d = decl V N T ; d = def V N T B),
                         coq.name->id N h) Names,
  std.map Sels psel-sel Sels1,
  sel-hyps Ctx Sels1 Hs, revert Ctx Hs G C, path-parts Ctx Hs G Parts,
  std.map Sels (s\ lw\ sigma L W\ path-locate Ctx Hs Parts s L W, lw = pr L W)
    LWs,
  std.map LWs fst Ls, std.map-filter LWs (lw\ w\ lw = pr _ w, not (w = "")) Ws,
  std.map Ls loc-path Ps,
  (nested Ps, !,
   coq.ltac.fail 0 {msg "the two selections are the same subterm or one is inside the other"} ; true).

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

% [avoid-names Hs Parts Avoid] Avoid are the names the variables of a
% pattern must not take: the hypotheses Hs and the words of the parts
pred avoid-names i:list string, i:list part, o:list string.
avoid-names Hs Parts Avoid :-
  std.map Parts (p\ ws\ sigma B T Shs S\ p = part B T Shs,
                   coq.term->string T S, identifiers S ws) Idss,
  std.flatten [Hs|Idss] Avoid.

% [pattern-of Avoid Ctx M Ps T Vis Pat] Pat is the pattern [X in ...] (or
% [X Y in ...]) of the term T whose selections are at the paths Ps, Vis
% being the paths of its printed subterms; it is checked (Ctx, M: as for
% pattern-text)
pred pattern-of i:list string, i:list string, i:bmode, i:list (list int),
                i:term, i:list (list int), o:string.
pattern-of Avoid Ctx M Ps T Vis Pat :-
  std.length Ps K, std.take K ["X", "Y"] Bases, fresh-names Bases Avoid Ns,
  std.string.concat " " Ns NsS,
  (pattern-checked Ns NsS Ctx M Ps T Vis Pat, ! ;
   % (neither passes the check: the error of the plain one)
   pattern-text Ns Ctx M Ps T Vis [] Body,
   Pat is "[" ^ NsS ^ " in " ^ Body ^ "]", check Pat Ps T).

% [pattern-checked Ns NsS Ctx M Ps T Vis Pat] Pat is the pattern of
% pattern-of, its variables Ns (NsS: with blanks between them), that passes
% check: the plain one, else, when the plain one does not elaborate and
% the selections are the scrutinees of matches whose branches bind no
% variable (if X then _ else _: the text alone does not give the type of
% X), the one where the variables are written with their types, (X : T)
% (annotated).  (Not the scrutinee of a let '(a, b) := X: ssreflect's
% patterns cannot go through such a match, the selection is widened.)
pred pattern-checked i:list string, i:string, i:list string, i:bmode,
                     i:list (list int), i:term, i:list (list int), o:string.
pattern-checked Ns NsS Ctx M Ps T Vis Pat :-
  pattern-text Ns Ctx M Ps T Vis [] Body0,
  Pat0 is "[" ^ NsS ^ " in " ^ Body0 ^ "]",
  S0 is "(" ^ Pat0 ^ ")", coq.parse.argument S0 ff "" A D,
  (D = ok, !, A = trm P0, check-open P0 Ps Ps [] T, Pat = Pat0 ;
   D = error _, std.forall Ps (scrutinee-of-if T),
   (pbp-annotate => pattern-text Ns Ctx M Ps T Vis [] Body1),
   Pat1 is "[" ^ NsS ^ " in " ^ Body1 ^ "]",
   check-ok Pat1 Ps T, Pat = Pat1).

% [scrutinee-of-if T P] the subterm at path P of T is the scrutinee of a
% match whose branches bind no variable (an if)
pred scrutinee-of-if i:term, i:list int.
scrutinee-of-if (match _ _ Bs) [0] :- !,
  std.forall Bs (b\ not (b = fun _ _ _)).
scrutinee-of-if T [I|P] :- kids T Ks, std.nth I Ks K,
  (K = kt U, scrutinee-of-if U P ; K = kb _ _ F, pi x\ scrutinee-of-if (F x) P).

% [annotated T R0 R] R is the variable of a pattern R0 (applied to the
% variables bound above it) at the place of the subterm T, written with the
% type of T (a cast, which Rocq-Elpi sees as let _ : Ty := R0 in _) when
% pbp-annotate holds, R0 otherwise
pred pbp-annotate.
pred annotated i:term, i:term, o:term.
annotated T R0 (let `_` Ty R0 (x\ x)) :- pbp-annotate, coq.typecheck T Ty ok, !.
annotated _ R R.

% [point-pattern In Pat] Pat is the pattern of the selections in the goal
% with their hypotheses generalized (the one of pbp)
pred point-pattern i:point-in, o:string.
point-pattern (point-in Names Hs C Parts Ls) Pat :-
  std.map Parts (p\ vs\ sigma B T Shs\ p = part B T Shs,
                   std.map Shs (sh\ v\ sigma P\ sh = shown P _ _ _,
                                         std.append B P v) vs) Viss,
  std.flatten Viss Vis,
  avoid-names Hs Parts Avoid, std.map Ls loc-path Ps, std.length Hs N,
  pattern-of Avoid Names (bm-goal N) Ps C Vis Pat.

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
  point-part In I, std.nth I Parts (part _ T Shs), std.length Hs N,
  (I = N, !, M = bm-goal 0 ; M = bm-hyp),
  std.map Shs (sh\ v\ sh = shown v _ _ _) Vis,
  avoid-names Hs Parts Avoid,
  std.map Ls (l\ p\ l = loc _ _ p) Ps,
  pattern-of Avoid Names M Ps T Vis Pat.

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
head-at [I|P] T GR :- kids T Ks, std.nth I Ks K, kid-head P K GR.

pred kid-head i:list int, i:kid, o:gref.
kid-head P (kt T) GR :- head-at P T GR.
kid-head P (kb N Ty B) GR :- pi x\ decl x N Ty => head-at P (B x) GR.

pred head-gref i:term, o:gref.
head-gref (global GR) GR.
head-gref (pglobal GR _) GR.
head-gref (app [H|_]) GR :- head-gref H GR.

/* ---------------- The pbp call ---------------- */

% [fresh-names Bases Avoid Ns] Ns are the names Bases, each with a number
% if needed, to avoid the names Avoid
pred fresh-names i:list string, i:list string, o:list string.
fresh-names [] _ [].
fresh-names [B|Bs] Avoid [N|Ns] :-
  fresh-name B Avoid 0 N, fresh-names Bs [N|Avoid] Ns.

% [fresh-name B Avoid I N] N is B, or B followed by a number from I, not in
% Avoid
pred fresh-name i:string, i:list string, i:int, o:string.
fresh-name B Avoid _ B :- not (std.mem! Avoid B), !.
fresh-name B Avoid I N :-
  N1 is B ^ int_to_string I, not (std.mem! Avoid N1), !, N = N1.
fresh-name B Avoid I N :- I1 is I + 1, fresh-name B Avoid I1 N.

% [nested Ps] two of the paths Ps are the same or one is inside the other
pred nested i:list (list int).
nested Ps :-
  std.mem Ps P, std.mem Ps Q, not (P == Q), std.appendR P _ Q.
nested [P, P].

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
   (pointing) or two (linking); a selection is [S E], the characters S to
   E (excluded) of the printed conclusion, or [H S E], those of the printed
   type of the hypothesis H; the characters are counted without the blanks,
   from 0; an empty range (S = E) is a click on the character S.  A
   selection that is not a subterm is widened to the smallest subterm that
   contains it, with a warning (pbp-widened).  The goal is unchanged. *)
Elpi Tactic pbp_pattern.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ Args as G) [seal G] :-
  parse-sels Args Sels, pbp-line Ctx Ty Sels Line Ws,
  std.forall Ws (w\ coq.warning "pbp" "pbp-widened"
                      "pbp_pattern: the selection is widened to" w),
  coq.say Line.
}}.

(* [elpi pbp_pattern_expect Line Ws Sel ...], for the tests: fails unless
   pbp_pattern gives the line Line, with the widened subterms Ws (separated
   by " / ", "" for none) *)
Elpi Tactic pbp_pattern_expect.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate lp:{{
solve (goal Ctx _ Ty _ [str Exp, str ExpW | Args] as G) [seal G] :-
  parse-sels Args Sels, pbp-line Ctx Ty Sels Line Ws,
  std.string.concat " / " Ws W,
  ((Line = Exp, W = ExpW), ! ;
   coq.ltac.fail 0 "pbp_pattern_expect: got" Line W "expected" Exp ExpW).
}}.
