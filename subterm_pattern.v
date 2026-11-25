(* From a path in a term to an ssreflect pattern that designates it.

   Paths.  A path "i.j.k" designates a subterm of a term: the positions
   of the immediate subterms to go through, from the root (kids below):
   in an application the head is 0 and the arguments 1, 2, ...; in a
   forall or a fun the name of the binder is 0, its type 1, its body 2;
   in a let the name 0, the type 1, the value 2, the body 3; in a match
   the scrutinee 0, the return type 1, the branches 2, 3, ...; in a cast
   (t : T) the type 0 and the term 1.  These are the paths that Rocq's
   Set Printing Subterm Paths puts on the printed subterms.

   Patterns.  A pattern [X in C] designates a subterm too: the one at the
   place of X in C.  The pattern of a path is the term where
   - the selected subterm becomes X, applied to the variables bound above
     it that it uses (X n under forall n);
   - the nodes on the path to it are kept;
   - the subterms beside the path become holes _ when they are printed,
     and are kept as they are when they are not (the implicit arguments
     that kept keeps, the return type of a match, the binders of a
     branch);
   then it is printed (default printing options, the holes pbp_hole
   printed _) and checked: its text is parsed and elaborated again, and
   it must give back the term with X at the selected place.  So the
   subterm at the place of X in the pattern is the subterm at the path,
   or the one it is widened to (below).

   The fallback chain (path-pattern), when the plain pattern of the path
   does not pass the check:
   1. the plain pattern of the path;
   2. the nearest subterm above it that is printed with the same text (an
      invisible coercion: Z.of_nat n printed n), its plain pattern;
   3. the pattern of the path with the types written, (X : T) and
      (_ : T), then only the types it needs (typed-reduce, by halves);
   4. the nearest subterm above it that can be selected (1 or 3) and is
      printed as a whole: the selection is widened, with a warning.

   Names.  The variables of a pattern are X (and Y for two selections):
   they are reserved, a binder of the pattern named X or Y is renamed (as
   display-names renames the binders named as hypotheses); only when a
   hypothesis or a constant named X is printed in the pattern does the
   variable become X0 (X1, ...).  A binder named as a hypothesis that its
   body uses is renamed as Rocq's goal display renames it (display-names).

   The code is the Elpi file subterm_pattern.elpi, to accumulate in a
   program or a database; it does not depend on pbp. *)

From Stdlib Require Import ssreflect.
From elpi Require Import elpi.

(* A pattern [X in C] (or [X Y in C]) is read as the function
   fun X => C (fun X Y => C) *)
Notation "'[' x .. y 'in' p ']' " :=
  ( (fun x => .. ( (fun y => p)) ..))
  (x binder, y binder, right associativity).

(* The marker of the holes of a pattern: it prints as its name only *)
Definition pbp_hole {A : Type} {a : A} : A := a.

Elpi File subterm_pattern.elpi lp:{{

/* ---------------- Messages ---------------- */

% [tool-name T] the errors start with T, the name of the tactic that is
% run (each tactic sets it for its own messages)
pred tool-name o:string.
tool-name "subterm_pattern".

% [msg S M] M is the message S, after the name of the tactic
pred msg i:string, o:string.
msg S M :- tool-name T, !, M is T ^ ": " ^ S.

/* ---------------- Strings ---------------- */

% [flat S F] F is S without its blanks
pred flat i:string, o:string.
flat S F :- rex.replace "[ \t\n\r]+" "" S F.

% [one-line S L] L is S on one line: each run of blanks is one space
pred one-line i:string, o:string.
one-line S L :- rex.replace "[ \t\n\r]+" " " S L.

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

% [contains S T] the string T occurs in S
pred contains i:string, i:string.
contains S T :- rex.match {calc (".*" ^ T ^ ".*")} S.

% [same-print A B] the texts A and B (without blanks) are the same, B
% possibly in parentheses
pred same-print i:string, i:string.
same-print A A :- !.
same-print A B :- B is "(" ^ A ^ ")".

/* ---------------- Subterms and paths ---------------- */

kind kid type.
type kt term -> kid.                           % an immediate subterm
type kb name -> term -> (term -> term) -> kid. % one under a binder: its
                                               % name, its type, the body
type kn name -> kid.                           % the name of a binder

% [kids T Ks] Ks are the immediate subterms of T
pred kids i:term, o:list kid.
kids (app L) Ks :- !, std.map L (t\ k\ k = kt t) Ks.
kids (prod N T F) [kn N, kt T, kb N T F] :- !.
kids (fun N T F) [kn N, kt T, kb N T F] :- !.
kids (let N T B F) [kt T, kt B, kb N T F] :- cast-let N F, !.
kids (let N T B F) [kn N, kt T, kt B, kb N T F] :- !.
kids (match T R Bs) [kt T, kt R | Ks] :- !,
  std.map Bs (t\ k\ k = kt t) Ks.
kids _ [].

% [rebuild T Ks T1] T1 is T with the immediate subterms Ks
pred rebuild i:term, i:list kid, o:term.
rebuild (app _) Ks T :- !,
  std.map Ks (k\ t\ k = kt t) [H|Args], mk-app H Args T.
rebuild (prod N _ _) [kn _, kt T, kb _ _ F] (prod N T F) :- !.
rebuild (fun N _ _) [kn _, kt T, kb _ _ F] (fun N T F) :- !.
rebuild (let N _ _ _) [kt T, kt B, kb _ _ F] (let N T B F) :- !.
rebuild (let N _ _ _) [kn _, kt T, kt B, kb _ _ F] (let N T B F) :- !.
rebuild (match _ _ _) [kt T, kt R | Ks] (match T R Bs) :- !,
  std.map Ks (k\ t\ k = kt t) Bs.
rebuild T [] T.

% [mk-app H Args T] T is H applied to Args, as one application; unlike
% coq.mk-app, a head fun or let is not reduced ((fun x => x + y) a stays)
pred mk-app i:term, i:list term, o:term.
mk-app H [] H :- !.
mk-app (app L) Args (app L1) :- !, std.append L Args L1.
mk-app H Args (app [H|Args]).

% [cast-let N F] a let named N of body F is a cast: Rocq-Elpi sees the
% cast (t : T) as let _ : T := t in x (its name is anonymous, its body its
% variable; a let k := t in k has a name)
pred cast-let i:name, i:(term -> term).
cast-let N F :- coq.name->id N "_", pi x\ F x == x.

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

% [parent P Q] Q is the path just above the path P (not the root)
pred parent i:list int, o:list int.
parent P Q :- std.rev P [_|R], std.rev R Q.

% [replace-at P Bs F T T1] T1 is T where its subterm S at path P is
% replaced by R, with F Bs' S R, Bs' being Bs and the variables bound above
% S (the outermost first)
pred replace-at i:list int, i:list term,
                i:(pred i:list term, i:term, o:term), i:term, o:term.
replace-at [] Bs F T R :- !, F Bs T R.
replace-at [I|P] Bs F T T1 :-
  kids T Ks, std.split-at I Ks Before [K|After], not (K = kn _),
  replace-kid P Bs F K K1,
  std.append Before [K1|After] Ks1, rebuild T Ks1 T1.

% [replace-kid P Bs F K K1] replace-at in the immediate subterm K
pred replace-kid i:list int, i:list term,
                 i:(pred i:list term, i:term, o:term), i:kid, o:kid.
replace-kid P Bs F (kt T) (kt T1) :- replace-at P Bs F T T1.
replace-kid P Bs F (kb N Ty B) (kb N Ty B1) :-
  pi x\ decl x N Ty =>
    sigma Bs1\ (std.append Bs [x] Bs1, replace-at P Bs1 F (B x) (B1 x)).

% [term-at P T R] R is the subterm of T at path P; it fails if R uses a
% variable bound in T
pred term-at i:list int, i:term, o:term.
term-at [] T T.
term-at [I|P] T R :- kids T Ks, std.nth I Ks K, kid-term P K R.

% [kid-term P K R] term-at in the immediate subterm K
pred kid-term i:list int, i:kid, o:term.
kid-term P (kt T) R :- term-at P T R.
kid-term P (kb _ _ B) R :- pi x\ term-at P (B x) R.

% [text-at P T S] S is the subterm of T at path P, printed on one line
pred text-at i:list int, i:term, o:string.
text-at [] T S :- coq.term->string T S0, one-line S0 S.
text-at [I|P] T S :- kids T Ks, std.nth I Ks K, kid-text P K S.

% [kid-text P K S] S is the subterm at path P of the subterm K
pred kid-text i:list int, i:kid, o:string.
kid-text P (kt T) S :- text-at P T S.
kid-text P (kb N Ty B) S :- pi x\ decl x N Ty => text-at P (B x) S.

% [name-at T P K] the path P of T ends at the name of a binder of kind K
% (forall, fun, let)
pred name-at i:term, i:list int, o:string.
name-at T [0] K :- binder-kind T K, !.
name-at T [I|P] K :- kids T Ks, std.length Ks L, I < L, std.nth I Ks Kd,
  (Kd = kt U, name-at U P K ; Kd = kb _ _ F, pi x\ name-at (F x) P K).

% [binder-kind T K] T is a binder of kind K (a cast is not one)
pred binder-kind i:term, o:string.
binder-kind (prod _ _ _) "forall".
binder-kind (fun _ _ _) "fun".
binder-kind (let N _ _ F) "let" :- not (cast-let N F).

% [through-name T P] the path P of T goes through the name of a binder
% (a longer path than one that ends at it)
pred through-name i:term, i:list int.
through-name T [0, _ | _] :- binder-kind T _, !.
through-name T [I|P] :- kids T Ks, std.length Ks L, I < L, std.nth I Ks Kd,
  (Kd = kt U, through-name U P ; Kd = kb _ _ F, pi x\ through-name (F x) P).

% [path-of-string S P] S is the path P written "i.j.k" ("" for the root)
pred path-of-string i:string, o:list int.
path-of-string "" [] :- !.
path-of-string S P :-
  rex.split "\\." S Ss,
  std.map Ss (s\ n\ (rex.match "^[0-9]+$" s, !, n is string_to_int s ;
                     coq.ltac.fail 0 {msg "not a path:"} S)) P.

% [string-of-path P S] S is the path P written "i.j.k"
pred string-of-path i:list int, o:string.
string-of-path P S :-
  std.map P (n\ s\ s is int_to_string n) Ss, std.string.concat "." Ss S.

/* ---------------- What is printed ---------------- */

kind status type.
type st-printed status.  % printed
type st-hidden status.   % never printed, nor anything in it: the return
                         % type of a match, the body of a cast (its
                         % variable, as Rocq-Elpi sees the cast)
type st-binder status.   % a binder of a branch of a match (the fun of the
                         % arguments of its constructor): not printed, nor
                         % its type (the constructor's), but its body is (a
                         % fun body: another binder of the branch)

% [kid-status T I St St1] St1 says how the I-th immediate subterm of T is
% printed, St how T is
pred kid-status i:term, i:int, i:status, o:status.
kid-status _ _ st-hidden st-hidden :- !.
kid-status (match _ _ _) 1 _ st-hidden :- !.
kid-status (match _ _ Bs) I _ st-binder :- I >= 2, J is I - 2,
  std.nth J Bs (fun _ _ _), !.
kid-status (let N _ _ F) 2 _ st-hidden :- cast-let N F, !.
kid-status (fun _ _ _) 1 st-binder st-hidden :- !.
kid-status (fun _ _ F) 2 st-binder st-binder :-
  pi x\ sigma N Ty B\ F x = fun N Ty B, !.
kid-status _ _ _ st-printed.

% [printed-at T P] the subterm at path P of T is printed
pred printed-at i:term, i:list int.
printed-at T P :- status-at T P st-printed st-printed.

% [status-at T P St0 St] St says how the subterm at path P of T is
% printed, St0 how T is
pred status-at i:term, i:list int, i:status, o:status.
status-at _ [] St St.
status-at T [I|P] St0 St :- kids T Ks, std.nth I Ks K, kid-status T I St0 St1,
  (K = kt U, status-at U P St1 St ;
   K = kb _ _ F, pi x\ status-at (F x) P St1 St).

% [marker-names O A B] A and B, the names of the two markers, are names
% that do not occur in O, the printed term (without blanks): so the
% printer neither renames a binder of the term nor mixes them with its text
pred marker-names i:string, o:string, o:string.
marker-names O A B :- marker-fresh O "pbp_mark" 0 A, marker-fresh O "pbp_end" 0 B.

% [marker-fresh O Base N Name] Name is Base, or Base with a number from
% N, that does not occur in O
pred marker-fresh i:string, i:string, i:int, o:string.
marker-fresh O Base 0 Name :- not (contains O Base), !, Name = Base.
marker-fresh O Base N Name :- N > 0, std.any->string N NS, C is Base ^ NS,
  not (contains O C), !, Name = C.
marker-fresh O Base N Name :- N1 is N + 1, marker-fresh O Base N1 Name.

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

kind printing type.
% [printing O A B] the printing O of a term, without blanks, and two
% marker names A and B that do not occur in it
type printing string -> string -> string -> printing.

% [printing-of T Pr] Pr is the printing of T
pred printing-of i:term, o:printing.
printing-of T (printing O A B) :-
  coq.term->string T S, flat S O, marker-names O A B.

% [whole-text T Pr P Before Txt] the subterm at path P of T (printed as Pr
% says) is printed as a whole: as Txt (without blanks), after the text
% Before (a subterm that is not printed has no text: marking it would
% break the printing of its match)
pred whole-text i:term, i:printing, i:list int, o:string, o:string.
whole-text T (printing O A B) P Before Txt :- printed-at T P,
  marked-string A B P T MF,
  around-mark A B MF Pre Post, fits O Pre Post Before Txt.

/* ---------------- The names of the binders ----------------
   Rocq-Elpi prints a binder whose name is the name of a hypothesis of
   the goal under a name of its own (elpi_ctx_entry_3_), where the goal
   display (Rocq's) names it as Rocq does: in the conclusion, with a new
   name (x0, Rocq avoids the names of the hypotheses there); in the type
   of a hypothesis, with its own name, unless the hypothesis of that name
   occurs under it (then a new name).  Such a binder is printed under a
   placeholder name, which is then replaced by that name. */

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
% (a hole is printed _: nothing in it is printed, its names stay)
display-names _ _ _ ({{ @pbp_hole lp:_ lp:_ }} as T) T R R :- !.
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
display-names Ctx Sc M (fix N I Ty F) (fix N1 I Ty1 F1) R0 R :- !,
  display-names Ctx Sc M Ty Ty1 R0 R1,
  display-binder Ctx Sc M N F N1 Sc1 R1 R2,
  pi x\ display-names Ctx Sc1 M (F x) (F1 x) R2 R.
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

% [kid-var-named-in S K] var-named-in in the immediate subterm K
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

% [fresh-ident-from Base I Avoid D] D is Base with the first number from
% I that makes it a name not in Avoid
pred fresh-ident-from i:string, i:int, i:list string, o:string.
fresh-ident-from Base I Avoid D :-
  D1 is Base ^ int_to_string I, not (std.mem! Avoid D1), !, D = D1.
fresh-ident-from Base I Avoid D :- I1 is I + 1, fresh-ident-from Base I1 Avoid D.

% [fresh-names Bases Avoid Ns] Ns are the names Bases, each with a number
% if needed (from 0), to avoid the names Avoid
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

% [kid-text-names Ctx M P K S] text-at-names in the immediate subterm K
pred kid-text-names i:list string, i:bmode, i:list int, i:kid, o:string.
kid-text-names Ctx M P (kt T) S :- text-at-names Ctx M P T S.
kid-text-names Ctx M P (kb N Ty B) S :-
  % the binder named as the display names it
  display-binder Ctx [] M N B _ [D|_] [] _, coq.id->name D ND,
  pi x\ decl x ND Ty => text-at-names [D|Ctx] M P (B x) S.

% [kid-mode M T I M1] M1 says where the I-th immediate subterm of T is, M
% where T is (the type of a generalized hypothesis, the rest after it)
pred kid-mode i:bmode, i:term, i:int, o:bmode.
kid-mode (bm-goal K) (prod _ _ _) 1 bm-hyp :- K > 0, !.
kid-mode (bm-goal K) (prod _ _ _) 2 (bm-goal K1) :- K > 0, !, K1 is K - 1.
kid-mode M _ _ M.

/* ---------------- The pattern ---------------- */

% [kept T I] the I-th immediate subterm of T stays as it is in the
% pattern, when it holds no selection: the head of an application, the
% type of a dependent binder or of a let, the return type of a match, the
% body of a cast (Rocq-Elpi sees the cast (t : T) as let _ : T := t in _
% whose body is the bound variable: so it prints back as a cast)
pred kept i:term, i:int.
kept (app _) 0.
kept (prod _ _ F) 1 :- pi x\ occurs x (F x).
kept (fun _ _ F) 1 :- pi x\ occurs x (F x).
kept (let N _ _ F) 0 :- cast-let N F, !.
kept (let N _ _ F) 2 :- cast-let N F, !.
kept (let _ _ _ _) 1.
kept (match _ _ _) 1.

kind pacc type.
% [pacc K Ns] what the walk has met so far: K places where a type may be
% written (the selections and the holes), the names Ns printed
type pacc int -> list string -> pacc.

% [typed-set Is] the types of the places number Is (from 0, in the order
% of the walk) are written
pred typed-set o:list int.

% [walk-bound X] X is a variable bound by the term walked (not a name of
% the context)
pred walk-bound o:term.

% [walk Sels St Bs T R A0 A] R is the pattern of T, printed as St says,
% Bs being the variables bound above it (the innermost first); Sels are
% the selections in T, each the pair of its path in T and its variable; A
% is A0 with what the walk meets
pred walk i:list (pair (list int) term), i:status, i:list term, i:term,
          o:term, i:pacc, o:pacc.
walk Sels _ Bs T R A0 A :- selected Sels X, !,
  std.rev Bs Bs1, std.filter Bs1 (v\ occurs v T) Vs, coq.mk-app X Vs R0,
  place T R0 R A0 A.
walk [] st-printed _ T R A0 A :- !, place T {{ @pbp_hole Prop lp:T }} R A0 A.
walk [] st-hidden _ T T A0 A :- !, names-in T A0 A.
walk Sels St Bs T R A0 A :- kids T Ks,
  (Ks = [], !, R = T, names-in T A0 A ;
   walk-kids Sels St Bs T 0 Ks Ks1 A0 A, rebuild T Ks1 R).

% [selected Sels X] one of the selections Sels is here (its path is
% empty): its variable is X
pred selected i:list (pair (list int) term), o:term.
selected [pr [] X | _] X :- !.
selected [_ | Sels] X :- selected Sels X.

% [walk-kids Sels St Bs T I Ks Ks1 A0 A] Ks1 are the patterns of Ks, the
% immediate subterms of T from the I-th
pred walk-kids i:list (pair (list int) term), i:status, i:list term,
               i:term, i:int, i:list kid, o:list kid, i:pacc, o:pacc.
walk-kids _ _ _ _ _ [] [] A A.
walk-kids Sels St Bs T I [K|Ks] [K1|Ks1] A0 A :-
  std.map-filter Sels (s\ r\ sigma P X\ s = pr [I|P] X, r = pr P X) SelsI,
  (SelsI = [], kept T I, !, K1 = K, kid-names K A0 A1 ;
   kid-status T I St StI, walk-kid SelsI StI Bs K K1 A0 A1),
  I1 is I + 1, walk-kids Sels St Bs T I1 Ks Ks1 A1 A.

% [walk-kid Sels St Bs K K1 A0 A] walk in the immediate subterm K (a
% binder: its variable is declared and bound)
pred walk-kid i:list (pair (list int) term), i:status, i:list term,
              i:kid, o:kid, i:pacc, o:pacc.
walk-kid _ _ _ (kn N) (kn N) A A.
walk-kid Sels St Bs (kt U) (kt R) A0 A :- walk Sels St Bs U R A0 A.
walk-kid Sels St Bs (kb N Ty F) (kb N Ty F1) A0 A :-
  pi x\ decl x N Ty => walk-bound x => walk Sels St [x|Bs] (F x) (F1 x) A0 A.

% [place T R0 R A0 A] R is R0, the variable or the hole in place of T,
% written with the type of T (a cast, which Rocq-Elpi sees as
% let _ : Ty := R0 in _) when typed-set says so; A counts the place
pred place i:term, i:term, o:term, i:pacc, o:pacc.
place T R0 R (pacc K Ns) (pacc K1 Ns) :- K1 is K + 1,
  (typed-set Is, std.mem! Is K, coq.typecheck T Ty ok, !,
   R = let `_` Ty R0 (x\ x) ; R = R0).

% [names-in T A0 A] A is A0 with the names of the constants and of the
% hypotheses that T uses
pred names-in i:term, i:pacc, o:pacc.
names-in (global GR) (pacc K Ns) (pacc K [S|Ns]) :- !, coq.gref->id GR S.
names-in (pglobal GR _) (pacc K Ns) (pacc K [S|Ns]) :- !, coq.gref->id GR S.
names-in T (pacc K Ns) (pacc K [S|Ns]) :- name T, not (walk-bound T),
  (decl T N _ ; def T N _ _), !, coq.name->id N S.
names-in T A0 A :- kids T Ks, std.fold Ks A0 kid-names A.

% [kid-names K A0 A] names-in in the immediate subterm K
pred kid-names i:kid, i:pacc, o:pacc.
kid-names (kn _) A A.
kid-names (kt T) A0 A :- names-in T A0 A.
kid-names (kb _ _ F) A0 A :- pi x\ walk-bound x => names-in (F x) A0 A.

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

% [pattern-build Ctx M Ps T Ts Ns Pat N] Pat is the text of the pattern
% of T whose selections are at the paths Ps, the types of its places Ts
% written; Ns are the names of its variables, N its number of places; Ctx
% are the names of the hypotheses and M says where T is (display-names)
pred pattern-build i:list string, i:bmode, i:list (list int), i:term,
                   i:list int, o:list string, o:string, o:int.
pattern-build Ctx M Ps T Ts Ns Pat N :-
  std.length Ps K, with-vars K [] (build-body Ctx M Ps T Ts Ns Body N),
  std.string.concat " " Ns NsS, Pat is "[" ^ NsS ^ " in " ^ Body ^ "]".

% [with-vars K Xs G] G Xs', Xs' being Xs then K new variables
pred with-vars i:int, i:list term, i:(pred i:list term).
with-vars 0 Xs G :- !, G Xs.
with-vars K Xs G :- K1 is K - 1, pi x\ sigma Xs1\ std.append Xs [x] Xs1, with-vars K1 Xs1 G.

% [build-body Ctx M Ps T Ts Ns Body N Xs] Body is the text of the body of
% the pattern of pattern-build, Xs being its variables
pred build-body i:list string, i:bmode, i:list (list int), i:term,
                i:list int, o:list string, o:string, o:int, i:list term.
build-body Ctx M Ps T Ts Ns Body N Xs :-
  std.map2 Ps Xs (p\ x\ s\ s = pr p x) Sels,
  (typed-set Ts => walk Sels st-printed [] T R (pacc 0 []) (pacc N Ids)),
  std.length Xs K, std.take K ["X", "Y"] Bases, fresh-names Bases Ids Ns,
  std.map2 Xs Ns (x\ n\ c\ sigma Nm\ coq.id->name n Nm, c = decl x Nm {{ Prop }}) Ds,
  % (the names of the variables are reserved: a binder of that name is renamed)
  std.append Ns Ctx Ctx1,
  (Ds => (display-names Ctx1 [] M R R1 [] Rs,
         default-printing (coq.term->string R1 S))),
  rex.replace "pbp_hole" "_" S S1, replace-placeholders Rs S1 S2,
  one-line S2 Body.

% [pattern-unchecked] the patterns are not checked (an action that does
% not write one: any printed subterm can be selected)
pred pattern-unchecked.

% [check-ok Text Ps C] the pattern Text, parsed and elaborated, is C once
% its variables are the subterms at the paths Ps, at these places (a
% test: the unknowns and the constraints of the elaboration are dropped,
% else they would weigh on the next checks)
pred check-ok i:string, i:list (list int), i:term.
check-ok _ _ _ :- pattern-unchecked, !.
check-ok Text Ps C :-
  S is "(" ^ Text ^ ")",
  not (not (coq.parse.argument S ff "" A D, D = ok, A = trm Pat,
            check-open Pat Ps [] C)).

% [check Text Ps C] check-ok, or the error that says why not
pred check i:string, i:list (list int), i:term.
check Text Ps C :-
  S is "(" ^ Text ^ ")",
  coq.parse.argument S ff "" A D,
  (D = ok, A = trm Pat, !,
   (check-open Pat Ps [] C, ! ;
    coq.ltac.fail 0 {msg "the pattern does not give back the goal with the selection (a selected subterm that the rest of the goal depends on cannot be abstracted)"}) ;
   D = error M, !,
   coq.ltac.fail 0 {msg "the pattern"} Text "does not elaborate:" M ;
   coq.ltac.fail 0 {msg "the pattern"} Text "is not a term").

% [check-open Pat Ps Xs C] the body of the pattern Pat, once its first
% variables Xs are opened (one per path of Ps), is C with these variables
% at the paths Ps
pred check-open i:term, i:list (list int), i:list term, i:term.
check-open (fun N T F) Ps Xs C :- std.length Xs K, std.length Ps L, K < L, !,
  pi x\ decl x N T => sigma Xs1\ (std.append Xs [x] Xs1, check-open (F x) Ps Xs1 C).
check-open Body Ps Xs C :-
  std.fold2 Ps Xs C (p\ x\ c\ c1\ replace-at p [] (bs\ t\ r\ sigma Vs\
      std.filter bs (v\ occurs v t) Vs, coq.mk-app x Vs r) c c1) C1,
  coq.unify-eq Body C1 ok, !.

% [pattern-checked Ctx M Ps T Pat] Pat is the pattern of T whose
% selections are at the paths Ps that passes check: the plain one, else
% the one with types, as few as it needs (pattern-build: Ctx, M)
pred pattern-checked i:list string, i:bmode, i:list (list int), i:term,
                     o:string.
pattern-checked Ctx M Ps T Pat :-
  pattern-build Ctx M Ps T [] Ns Pat0 N,
  (check-ok Pat0 Ps T, !, Pat = Pat0 ; typed-pattern Ctx M Ps T Ns N Pat).

% [plain-pattern Ctx M Ps T Pat] the plain pattern Pat passes check
pred plain-pattern i:list string, i:bmode, i:list (list int), i:term,
                   o:string.
plain-pattern Ctx M Ps T Pat :-
  pattern-build Ctx M Ps T [] _ Pat _, check-ok Pat Ps T.

% [typed-pattern Ctx M Ps T Ns N Pat] Pat is the pattern with types
% that passes check, with as few types as it needs: all N places typed,
% then reduced (typed-reduce); Ns are its variables
pred typed-pattern i:list string, i:bmode, i:list (list int), i:term,
                   i:list string, i:int, o:string.
typed-pattern Ctx M Ps T Ns N Pat :-
  std.iota N All, typed-ok Ctx M Ps T Ns All, !,
  typed-reduce (typed-ok Ctx M Ps T Ns) All [] Need,
  pattern-build Ctx M Ps T Need Ns Pat _.

% [typed-ok Ctx M Ps T Ns Ts] the pattern with the types of the places Ts
% passes check
pred typed-ok i:list string, i:bmode, i:list (list int), i:term,
              i:list string, i:list int.
typed-ok Ctx M Ps T Ns Ts :-
  pattern-build Ctx M Ps T Ts Ns P _, check-ok P Ps T.

% [typed-reduce Ok Cs Fs Need] Need are the places of Cs whose types the
% pattern needs (Ok: it passes check), the types at Fs being written: none
% if it passes without them, else those of each half of Cs in turn
pred typed-reduce i:(pred i:list int), i:list int, i:list int, o:list int.
typed-reduce _ [] _ [] :- !.
typed-reduce Ok _ Fs [] :- Ok Fs, !.
typed-reduce _ [C] _ [C] :- !.
typed-reduce Ok Cs Fs Need :-
  std.length Cs L, H is L div 2, std.split-at H Cs A B,
  std.append B Fs BFs, typed-reduce Ok A BFs NA,
  std.append NA Fs NAFs, typed-reduce Ok B NAFs NB,
  std.append NA NB Need.

% [pattern-of Ctx M Ps T Pat] Pat is the pattern [X in ...] (or [X Y in
% ...]) of T whose selections are at the paths Ps, checked: the error of
% check if neither the plain one nor the typed one passes it
pred pattern-of i:list string, i:bmode, i:list (list int), i:term,
                o:string.
pattern-of Ctx M Ps T Pat :- pattern-checked Ctx M Ps T Pat, !.
pattern-of Ctx M Ps T _ :-
  pattern-build Ctx M Ps T [] _ Pat _, check Pat Ps T, fail.

/* ---------------- The fallback chain ---------------- */

% [path-pattern Ctx M T P0 P Pat W] Pat is the pattern of the subterm at
% path P0 of T, or of the one at path P that it is widened to; W is the
% text of that subterm when the widening is seen ("" otherwise): the
% fallback chain of the header (Ctx, M: as for pattern-build)
pred path-pattern i:list string, i:bmode, i:term, i:list int,
                  o:list int, o:string, o:string.
path-pattern Ctx M T P0 P Pat W :-
  (printed-at T P0, plain-pattern Ctx M [P0] T Pat0, !, P = P0, Pat = Pat0, W = "" ;
   P0 = [_|_], text-at P0 T S0, flat S0 Txt0, printing-of T Pr,
   (parent P0 Q, same-print-up Ctx M T Pr Txt0 Q P1 Pat1, !, P = P1, Pat = Pat1, W = "" ;
    printed-at T P0, pattern-checked Ctx M [P0] T Pat2, !, P = P0, Pat = Pat2, W = "" ;
    parent P0 Q, widen-from Ctx M T Pr Q P Pat Txt,
    (same-print Txt0 Txt, !, W = "" ; text-at-names Ctx M P T W))).

% [same-print-up Ctx M T Pr Txt Q P Pat] P is the nearest path from Q up
% whose subterm is printed as Txt and whose plain pattern Pat passes check
% (the subterms printed otherwise stop the search; those not printed as
% a whole, a coercion inside another, are passed)
pred same-print-up i:list string, i:bmode, i:term, i:printing, i:string,
                  i:list int, o:list int, o:string.
same-print-up Ctx M T Pr Txt Q P Pat :- whole-text T Pr Q _ TxtQ, !,
  same-print Txt TxtQ,
  (plain-pattern Ctx M [Q] T Pat0, !, P = Q, Pat = Pat0 ;
   parent Q Q1, same-print-up Ctx M T Pr Txt Q1 P Pat).
same-print-up Ctx M T Pr Txt Q P Pat :-
  parent Q Q1, same-print-up Ctx M T Pr Txt Q1 P Pat.

% [widen-from Ctx M T Pr Q P Pat Txt] P is the nearest path from Q up
% whose subterm is printed as a whole (as Txt, without blanks) and has a
% pattern Pat that passes check; the root at worst
pred widen-from i:list string, i:bmode, i:term, i:printing, i:list int,
                o:list int, o:string, o:string.
widen-from Ctx M T (printing O _ _) [] [] Pat O :- !,
  pattern-build Ctx M [[]] T [] _ Pat _.
widen-from Ctx M T Pr Q Q Pat Txt :-
  whole-text T Pr Q _ Txt, pattern-checked Ctx M [Q] T Pat, !.
widen-from Ctx M T Pr Q P Pat Txt :-
  parent Q Q1, widen-from Ctx M T Pr Q1 P Pat Txt.

}}.
