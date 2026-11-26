(* Subterm selectors: which subterms of a goal an ssreflect pattern selects.

   What a selector denotes.  A selector (an ssreflect pattern, Gonthier and
   Tassi, "A language of patterns for subterm selection", ITP 2012)
   denotes a SET of positions of the goal, not one position: the pattern
   [_ - b] denotes all the occurrences of its first instance (pre-order),
   so in (a - b) + (b - c) = (a - b) + (d - b) both occurrences of a - b
   (paper, Ex. 5).  A position is a path "i.j.k" as Rocq's Set Printing
   Subterm Paths tags the subterms (subterm_pattern.v: in an application
   the head is 0 and the arguments 1, 2, ...; forall/fun name 0, type 1,
   body 2; let name 0, type 1, value 2, body 3; match scrutinee 0, return
   type 1, branches 2, ...).

   The patterns are the c-patterns of the paper (its grammar, section 2.1):
     t                 a term pattern (B1 closed term, B2 term with holes,
                       B3 flexible head),
     X in C            C1, the X part of the first instance of C,
     t in X in C       C2, the first instance of t inside the X part of C,
     t as X in C       C3, the X part of the first instance of C[t/X],
   each one possibly after an occurrence switch {1 3} or {-2} (E1), and
   written alone, in parentheses or in brackets: "_ - b", "(_ - b)" and
   "[_ - b]" are the same pattern.  The kind names are those of
   ~/claudeExp/subterm-select/PATTERNS.md, section 7 (sel-kind below, the
   one place where they are written).

   The oracle.  The semantics is ssreflect's own, not a reimplementation:
   the pattern is given to ssreflect's set,
     set z := {occ}(pattern)          (in H for a hypothesis)
   on the goal itself, and the positions are the paths of the new local
   definition z in the goal that set gives: set puts z in place of each
   selected subterm, a leaf in place of a subterm, so the paths of the
   occurrences of z are the paths of the selected subterms in the
   ORIGINAL goal.  set is run on a scratch copy: a new goal sel_box Ty in
   the same context (Ty the conclusion, at path 2 of sel_box Ty; for a
   hypothesis, sel_box True, the hypothesis being in the context), closed
   by exact I afterwards, so the goal of the user is unchanged.  The text
   of the tactic is parsed and run by run_tactic_string
   (plugin/g_select.mlg): Rocq-Elpi calls an Ltac tactic by its name only,
   with terms or strings as arguments, never a tactic text to parse.
   Special cases:
   - no match: ssreflect's error is reported (not a crash);
   - a closed term that does not occur: set adds the definition and
     abstracts nothing: "nothing selected";
   - z can replace a prefix of an application (the pattern f a in f a b):
     the position is then the path of the application and the number of
     its last arguments left out, written P<K (all of them left out: the
     head, written P.0);
   - a selected subterm that the goal display does not print (an implicit
     argument, the return type of a match) is flagged "(not printed)": no
     tag of the printer shows its path.

   Univocal.  A pattern is univocal when it selects exactly one position.

   Fragility (paper, Ex. 2).  A pattern selects the first instance of its
   outer term (t for B; C, with X a hole, for C1 and C2; C[t/X] for C3);
   the LATER instances of that term, after the first one in pre-order, are
   what the pattern would select if the goal changed before them.  They
   are computed by the same oracle: for each subterm s of the goal after
   the first selected position (pre-order) that does not use a variable
   bound in the goal, the outer term is given to set on the scratch goal
   sel_box s; s is a later instance when set selects s itself, and the
   pattern, run on the same scratch goal, says what it would select there.
   The occurrences of the first instance are not later instances (the
   subterms inside them are tried).  The outer term is found by splitting
   the text of the pattern at its keywords in and as outside parentheses
   (a let ... in written inside the pattern would mislead the split: such a
   pattern is read as a term).

   Tactics (the goal is unchanged):
     elpi pattern_select "<pattern>".        in the conclusion
     elpi pattern_select "H" "<pattern>".    in the type of hypothesis H
   print the selected positions with their texts, "univocal" or "N
   positions", then the later instances.  For the tests:
     elpi pattern_select_expect ["H"] "<pattern>" "2.1 3.1".
     elpi pattern_select_later_expect ["H"] "<pattern>" "3.2 | 2.2.1".
     elpi pattern_select_fails ["H"] "<pattern>".
   fail unless the selected positions (in pre-order, separated by blanks,
   "" for none, "root" for the whole part) are the given ones; unless the
   positions selected in the later instances (one group per instance,
   separated by |) are; unless ssreflect refuses the pattern.

   The reverse: [elpi select_all "P"] (or "H" "P") lists the ways to
   designate the subterm at path P, one or more per kind, each one checked
   by the oracle, best first (section select_all below: the generation by
   anti-unification, the cost sg-cost). *)

Declare ML Module "coq-tmp.select".
From Stdlib Require Export ssreflect ssrmatching.
From elpi Require Import elpi.
From coq_tmp Require Export subterm_pattern.

(* the scratch goal of the later instances: s alone, so that the pattern
   is matched against s and its subterms only *)
Definition sel_box {A : Type} (a : A) : Prop := True.

Elpi File subterm_select.elpi lp:{{

/* ---------------- The kinds of selectors ---------------- */

% The names of the kinds (PATTERNS.md, section 7), in one place
kind sel-kind type.
type a1-path, a2-occurrence, a3-range sel-kind.
type b1-closed-term, b2-term-with-holes, b3-flexible-head, b4-type-driven sel-kind.
type c1-context, c2-redex-in-context, c3-redex-as-context sel-kind.
type d1-rewrite-in, d2-rewrite-in-context sel-kind.
type e1-occurrence-switch, e2-named-context sel-kind.

% [sel-kind-label K L] L is the label of the kind K in the outputs
pred sel-kind-label i:sel-kind, o:string.
sel-kind-label a1-path "A1 path".
sel-kind-label a2-occurrence "A2 occurrence".
sel-kind-label a3-range "A3 range".
sel-kind-label b1-closed-term "B1 closed term".
sel-kind-label b2-term-with-holes "B2 term with holes".
sel-kind-label b3-flexible-head "B3 flexible head".
sel-kind-label b4-type-driven "B4 type-driven".
sel-kind-label c1-context "C1 context".
sel-kind-label c2-redex-in-context "C2 redex in context".
sel-kind-label c3-redex-as-context "C3 redex as context".
sel-kind-label d1-rewrite-in "D1 rewrite-only in C".
sel-kind-label d2-rewrite-in-context "D2 rewrite-only in X in C".
sel-kind-label e1-occurrence-switch "E1 occurrence switch".
sel-kind-label e2-named-context "E2 named context".

/* ---------------- The text of a pattern ---------------- */

% The form of a pattern, from its text
kind sel-form type.
type sf-term string -> sel-form.                      % t
type sf-in string -> string -> sel-form.              % X in C
type sf-in-in string -> string -> string -> sel-form. % t in X in C
type sf-as-in string -> string -> string -> sel-form. % t as X in C

% A pattern read: its occurrence switch ("" for none), its text without
% the switch and the brackets, its form
kind sel-pat type.
type sel-pat string -> string -> sel-form -> sel-pat.

% [sel-trim S T] T is S without its blanks at both ends
pred sel-trim i:string, o:string.
sel-trim S T :- rex.replace "^[ \t\n\r]+" "" S S1, rex.replace "[ \t\n\r]+$" "" S1 T.

% [sel-chars S Cs] Cs are the characters (bytes) of S
pred sel-chars i:string, o:list string.
sel-chars S Cs :- N is size S, sel-chars-from S 0 N Cs.
pred sel-chars-from i:string, i:int, i:int, o:list string.
sel-chars-from _ N N [] :- !.
sel-chars-from S I N [C|Cs] :- C is substring S I 1, I1 is I + 1, sel-chars-from S I1 N Cs.

% [sel-depth C D D1] D1 is the depth of brackets after the character C,
% D the one before
pred sel-depth i:string, i:int, o:int.
sel-depth "(" D D1 :- !, D1 is D + 1.
sel-depth "[" D D1 :- !, D1 is D + 1.
sel-depth "{" D D1 :- !, D1 is D + 1.
sel-depth ")" D D1 :- !, D1 is D - 1.
sel-depth "]" D D1 :- !, D1 is D - 1.
sel-depth "}" D D1 :- !, D1 is D - 1.
sel-depth _ D D.

% [sel-first-close Cs I D J] J is the position of the character of Cs
% that brings the depth back to 0 (I the position of the first, D the
% depth before it)
pred sel-first-close i:list string, i:int, i:int, o:int.
sel-first-close [C|Cs] I D J :- sel-depth C D D1,
  (D1 = 0, !, J = I ; I1 is I + 1, sel-first-close Cs I1 D1 J).

% [sel-closing S O C] the text S starts with the bracket O whose closing
% bracket C ends S
pred sel-closing i:string, i:string, i:string.
sel-closing S O C :- starts-with O S, ends-with C S, N is size S,
  sel-chars S Cs, sel-first-close Cs 0 0 I, N1 is N - 1, I = N1.

% [sel-unwrap S T] T is S without the brackets or parentheses around it
pred sel-unwrap i:string, o:string.
sel-unwrap S T :- (sel-closing S "[" "]" ; sel-closing S "(" ")"), !,
  N is size S - 2, S1 is substring S 1 N, sel-trim S1 S2, sel-unwrap S2 T.
sel-unwrap S S.

% [sel-split-occ S Occ P] S is the occurrence switch Occ ({..}, or "")
% then the pattern P
pred sel-split-occ i:string, o:string, o:string.
sel-split-occ S Occ P :- starts-with "{" S, sel-chars S Cs, sel-first-close Cs 0 0 J, !,
  L is J + 1, Occ is substring S 0 L, R is size S - L,
  P0 is substring S L R, sel-trim P0 P.
sel-split-occ S "" S.

% [sel-keywords S Ks] Ks are the positions and words of the keywords in
% and as of S outside brackets, from the left
pred sel-keywords i:string, o:list (pair int string).
sel-keywords S Ks :- sel-chars S Cs, sel-kw Cs S 0 0 Ks.
pred sel-kw i:list string, i:string, i:int, i:int, o:list (pair int string).
sel-kw [] _ _ _ [].
sel-kw [C|Cs] S I D Ks :- sel-depth C D D1, I1 is I + 1,
  (D = 0, sel-blank C, sel-kw-at S I W, !, Ks = [pr I W | Ks1] ; Ks = Ks1),
  sel-kw Cs S I1 D1 Ks1.

pred sel-blank i:string.
sel-blank " ".
sel-blank "\t".
sel-blank "\n".

% [sel-kw-at S I W] the keyword W (in or as) follows the blank at I in S,
% then a blank
pred sel-kw-at i:string, i:int, o:string.
sel-kw-at S I W :- N is size S, I + 4 < N, J is I + 1, W is substring S J 2,
  (W = "in" ; W = "as"), K is I + 3, B is substring S K 1, sel-blank B.

% [sel-cut S I J T] T is the text of S from I to J (excluded), trimmed
pred sel-cut i:string, i:int, i:int, o:string.
sel-cut S I J T :- L is J - I, T0 is substring S I L, sel-trim T0 T.

% [sel-parse S P] P is the pattern of text S
pred sel-parse i:string, o:sel-pat.
sel-parse S0 (sel-pat Occ Txt F) :-
  sel-trim S0 S1, sel-unwrap S1 S2, sel-split-occ S2 Occ S3, sel-unwrap S3 Txt,
  sel-keywords Txt Ks, N is size Txt, sel-form-of Txt N Ks F.

% [sel-form-of Txt N Ks F] F is the form of the pattern Txt (of size N)
% whose keywords are Ks
pred sel-form-of i:string, i:int, i:list (pair int string), o:sel-form.
sel-form-of Txt _ [] (sf-term Txt) :- !.
sel-form-of Txt N [pr I "in"] (sf-in X C) :- !,
  sel-cut Txt 0 I X, J is I + 4, sel-cut Txt J N C.
sel-form-of Txt N [pr I W, pr I2 "in"] F :- !,
  sel-cut Txt 0 I T, J is I + 4, sel-cut Txt J I2 X, J2 is I2 + 4, sel-cut Txt J2 N C,
  (W = "in", !, F = sf-in-in T X C ; F = sf-as-in T X C).
sel-form-of Txt _ _ (sf-term Txt).

% [sel-form-text F S] S is the text of the pattern of form F
pred sel-form-text i:sel-form, o:string.
sel-form-text (sf-term T) T.
sel-form-text (sf-in X C) S :- S is X ^ " in " ^ C.
sel-form-text (sf-in-in T X C) S :- S is T ^ " in " ^ X ^ " in " ^ C.
sel-form-text (sf-as-in T X C) S :- S is T ^ " as " ^ X ^ " in " ^ C.

% [sel-form-kind F K] K is the kind of a pattern of form F; a term
% pattern is elaborated (its holes become unknowns): no hole, B1; a hole
% at its head, B3; else B2 (from the text when it does not elaborate
% alone)
pred sel-form-kind i:sel-form, o:sel-kind.
sel-form-kind (sf-term T) K :-
  coq.parse.argument {calc ("(" ^ T ^ ")")} ff "" (trm Tm) ok, !,
  (ground_term Tm, !, K = b1-closed-term ;
   Tm = app [H|_], var H, !, K = b3-flexible-head ;
   K = b2-term-with-holes).
sel-form-kind (sf-term T) b2-term-with-holes :- rex.match ".*\\b_\\b.*" T, !.
sel-form-kind (sf-term _) b1-closed-term.
sel-form-kind (sf-in _ _) c1-context.
sel-form-kind (sf-in-in _ _ _) c2-redex-in-context.
sel-form-kind (sf-as-in _ _ _) c3-redex-as-context.

% [sel-replace-var X R C C1] C1 is the text C with the identifier X
% replaced by R
pred sel-replace-var i:string, i:string, i:string, o:string.
sel-replace-var X R C C1 :- rex.replace {calc ("\\b" ^ X ^ "\\b")} R C C1.

% [sel-outer F T] T is the text of the outer term of a pattern of form F:
% the term matched first (header, Fragility)
pred sel-outer i:sel-form, o:string.
sel-outer (sf-term T) T.
sel-outer (sf-in X C) T :- sel-replace-var X "_" C T.
sel-outer (sf-in-in _ X C) T :- sel-replace-var X "_" C T.
sel-outer (sf-as-in E X C) T :- sel-replace-var X {calc ("(" ^ E ^ ")")} C T.

/* ---------------- The oracle ---------------- */

% A selected position: the path of a subterm, or a prefix of an
% application (its path, the number of its last arguments left out)
kind sel-pos type.
type sp-at list int -> sel-pos.
type sp-prefix list int -> int -> sel-pos.

% The result of a run of the oracle
kind sel-res type.
type sel-ok list sel-pos -> sel-res.
type sel-error string -> sel-res.

% [sel-name N] N is the name of the local definition that set adds
pred sel-name o:string.
sel-name "pattern_select_z".

% [sel-set-text H Occ P S] S is the tactic that sets z to the pattern of
% text P with the occurrence switch Occ, in hypothesis H ("" for the
% conclusion)
pred sel-set-text i:string, i:string, i:string, o:string.
sel-set-text H Occ P S :- sel-name Z,
  (H = "", !, In = "" ; In is " in " ^ H),
  S is "set " ^ Z ^ " := " ^ Occ ^ "(" ^ P ^ ")" ^ In.

% [sel-scratch C S Tac H R] runs the tactic Tac on a new goal sel_box S in
% the context C, and R are the positions of z in the goal it gives: in
% its conclusion (H = "", paths of sel_box S: S is at 2) or in the type of
% its hypothesis H.  The new goal is then closed (exact I: sel_box S is
% True), so it leaves nothing behind; the goal of the user is not touched.
% (Backtracking the proof state would be the other way: std.findall over
% an Ltac call is an anomaly of Rocq-Elpi 3.x.)
pred sel-scratch i:goal-ctx, i:term, i:string, i:string, o:sel-res.
sel-scratch _C S Tac H R :-
  (coq.typecheck S Ty ok,
        coq.typecheck E {{ @sel_box lp:Ty lp:S }} ok,
        coq.ltac.collect-goals E [SG] _),
  sel-scratch-sealed SG Tac H R, !.
sel-scratch _ _ _ _ (sel-error "the scratch goal could not be made").

pred sel-scratch-sealed i:sealed-goal, i:string, i:string, o:sel-res.
sel-scratch-sealed (nabla F) Tac H R :- pi x\ sel-scratch-sealed (F x) Tac H R.
sel-scratch-sealed (seal (goal C RE Ty E _ as G)) Tac H R :-
  coq.ltac.call-ltac1 "run_tactic_string" (goal C RE Ty E [str Tac]) GL D,
  (D = error M, !, one-line M M1, R = sel-error M1, sel-close (seal G) ;
   GL = [SG], !, sel-orig C Ty H O, sel-open SG H O R, sel-close SG ;
   R = sel-error "set gave several goals", std.forall GL sel-close).

% [sel-orig C Ty H O] O is the part, before set, of the goal of context C
% and conclusion Ty: Ty (H = "") or the type of the hypothesis H
pred sel-orig i:goal-ctx, i:term, i:string, o:term.
sel-orig _ Ty "" Ty :- !.
sel-orig C _ H T :- (std.mem C (decl _ N T) ; std.mem C (def _ N _ T)), coq.name->id N H, !.

% [sel-close SG] closes the scratch goal SG (exact I)
pred sel-close i:sealed-goal.
sel-close (nabla F) :- pi x\ sel-close (F x).
sel-close (seal (goal C RE Ty E _)) :-
  coq.ltac.call-ltac1 "run_tactic_string" (goal C RE Ty E [str "exact I"]) _ ok, !.
sel-close _.

% [sel-oracle G H Occ P R] R is what the pattern of text P (occurrence
% switch Occ) selects in the goal G (its hypothesis H, "" for the
% conclusion): the scratch goal is sel_box Ty for the conclusion Ty (the
% positions in Ty are those at 2 in it), sel_box True for a hypothesis
pred sel-oracle i:goal, i:string, i:string, i:string, o:sel-res.
sel-oracle (goal C _ Ty _ _) H Occ P R :- sel-set-text H Occ P Tac,
  (H = "", !, sel-scratch C Ty Tac "" R0, sel-box-map [] R0 R ;
   sel-scratch C {{ True }} Tac H R).

% [sel-open SG H O R] R are the positions of z in the goal SG (in the type
% of its hypothesis H if H is not ""), O the part before set
pred sel-open i:sealed-goal, i:string, i:term, o:sel-res.
sel-open (nabla F) H O R :- pi x\ sel-open (F x) H O R.
sel-open (seal (goal Ctx _ Ty _ _)) H O R :- sel-name ZN,
  std.mem Ctx (def Z NZ _ ZB), coq.name->id NZ ZN, !, sel-lambdas ZB NL,
  (H = "", !, T = Ty ;
   std.mem Ctx (decl _ NH T), coq.name->id NH H, ! ;
   std.mem Ctx (def _ NH _ T), coq.name->id NH H),
  !, sel-occs Z NL [] T O [] [] Ps0, std.rev Ps0 Ps, R = sel-ok Ps.
sel-open _ _ _ (sel-error "set did not add its definition").

% [sel-occs Z NL Bs T O Rev A0 A] A is A0 with the positions of Z in T
% (Rev: the path of T, reversed; Bs the variables bound above T), in
% pre-order, the last first; O is the subterm of the original goal at the
% same place: set erases a cast (t : T) around a subterm it abstracts,
% (z in place of the cast is read as the cast: it may be its term, flagged),
% so where O is a cast and T is not, T is read as the term of the cast (its
% index 1).  Z x1 .. xk, the xi bound variables and Z's body a fun of NL
% >= k arguments, is the subterm there abstracted over the variables it
% uses (set abstracts a subterm under binders so); Z a1 .. ak otherwise is
% a prefix of an application
pred sel-occs i:term, i:int, i:list term, i:term, i:term, i:list int,
              i:list sel-pos, o:list sel-pos.
sel-occs Z NL Bs T (let N _ B F) Rev A A1 :- cast-let N F, not (T = let _ _ _ _), not (T = Z), !,
  sel-occs Z NL Bs T B [1|Rev] A A1.
sel-occs Z _ _ Z _ Rev A [sp-at P|A] :- !, std.rev Rev P.
sel-occs Z NL Bs (app [Z|Args]) O Rev A [sp-at P|A] :-
  not (O = app [_|Args]),  % else Z is the head of the original application
  std.length Args K, K =< NL, std.forall Args (a\ std.mem! Bs a), !, std.rev Rev P.
sel-occs Z NL Bs (app [Z|Args]) O Rev A A1 :- !, std.rev Rev P, std.length Args K,
  % the arguments are the last K ones of the original application
  (O = app [_|OArgs], std.length OArgs N, N >= K, !, Sh is N - K, std.drop Sh OArgs OL ;
   Sh = 0, OL = Args),
  I0 is Sh + 1, sel-occs-args Z NL Bs Args OL Rev I0 [sp-prefix P K|A] A1.
sel-occs Z NL Bs T O Rev A A1 :- kids-fold T (sel-occs-kid Z NL Bs Rev O) A A1.

% [sel-occs-args Z NL Bs Ts Os Rev I A0 A] sel-occs in the arguments Ts
% (the original ones Os), the first at index I
pred sel-occs-args i:term, i:int, i:list term, i:list term, i:list term, i:list int, i:int,
                   i:list sel-pos, o:list sel-pos.
sel-occs-args _ _ _ [] _ _ _ A A.
sel-occs-args Z NL Bs [T|Ts] [O|Os] Rev I A A2 :-
  sel-occs Z NL Bs T O [I|Rev] A A1, I1 is I + 1, sel-occs-args Z NL Bs Ts Os Rev I1 A1 A2.

% [sel-occs-kid Z NL Bs Rev O T I K A0 A] sel-occs in the immediate subterm
% K (at I) of T, O being the original term in place of T
pred sel-occs-kid i:term, i:int, i:list term, i:list int, i:term, i:term, i:int, i:kid,
                  i:list sel-pos, o:list sel-pos.
sel-occs-kid Z NL Bs Rev O _ I K A A1 :-
  (kid-at O I (ko\ sel-occs-pair Z NL Bs [I|Rev] K ko A A1), ! ;
   sel-occs-pair Z NL Bs [I|Rev] K K A A1).

% [sel-occs-pair Z NL Bs Rev K KO A0 A] sel-occs in the subterm K, KO the
% original one
pred sel-occs-pair i:term, i:int, i:list term, i:list int, i:kid, i:kid,
                   i:list sel-pos, o:list sel-pos.
sel-occs-pair Z NL Bs Rev (kt T) (kt O) A A1 :- !, sel-occs Z NL Bs T O Rev A A1.
sel-occs-pair Z NL Bs Rev (kb _ _ F) (kb _ _ FO) A A1 :- !,
  pi x\ sel-occs Z NL [x|Bs] (F x) (FO x) Rev A A1.
sel-occs-pair Z NL Bs Rev (kt T) _ A A1 :- !, sel-occs Z NL Bs T T Rev A A1.
sel-occs-pair Z NL Bs Rev (kb _ _ F) _ A A1 :- !,
  pi x\ sel-occs Z NL [x|Bs] (F x) (F x) Rev A A1.
sel-occs-pair _ _ _ _ (kn _) _ A A.

% [sel-lambdas T N] T is a fun of N arguments (N >= 0)
pred sel-lambdas i:term, o:int.
sel-lambdas (fun _ _ F) N :- !, pi x\ sel-lambdas (F x) N1, N is N1 + 1.
sel-lambdas _ 0.

/* ---------------- Positions: texts, printing, order ---------------- */

% [sel-pos-string Q S] S is the position Q written as in the expectations
pred sel-pos-string i:sel-pos, o:string.
sel-pos-string (sp-at P) S :- string-of-path P S0, (S0 = "", !, S = "root" ; S = S0).
sel-pos-string (sp-prefix P K) S :- sel-pos-string (sp-at P) S0, S is S0 ^ "<" ^ {std.any->string K}.

% [sel-pos-path Q P] P is the path of the position Q (of the application,
% for a prefix)
pred sel-pos-path i:sel-pos, o:list int.
sel-pos-path (sp-at P) P.
sel-pos-path (sp-prefix P _) P.

% [sel-pos-text T Q S] S is the text of the position Q of T
pred sel-pos-text i:term, i:sel-pos, o:string.
sel-pos-text T (sp-at P) S :- text-at P T S, !.
sel-pos-text T (sp-prefix P K) S :- sel-prefix-at P K T S, !.
sel-pos-text _ _ "?".

% [sel-prefix-at P K T S] S is the text of the application at path P of T
% without its last K arguments
pred sel-prefix-at i:list int, i:int, i:term, o:string.
sel-prefix-at [] K (app L) S :- std.length L N, M is N - K, std.take M L L1,
  (L1 = [H], !, coq.term->string H S0 ; coq.term->string (app L1) S0),
  one-line S0 S.
sel-prefix-at [I|P] K T S :- kid-at T I (sel-prefix-kid P K S).
pred sel-prefix-kid i:list int, i:int, o:string, i:kid.
sel-prefix-kid P K S (kt T) :- sel-prefix-at P K T S.
sel-prefix-kid P K S (kb N Ty B) :- pi x\ decl x N Ty => sel-prefix-at P K (B x) S.

% [sel-hidden T P] the subterm at path P of T is not printed: an implicit
% argument, or a part of a term that the printer does not show
pred sel-hidden i:term, i:list int.
sel-hidden T P :- not (printed-at T P), !.
sel-hidden T P :- sel-implicit-on T P.

% [sel-implicit-on T P] the path P of T goes through an implicit argument
pred sel-implicit-on i:term, i:list int.
sel-implicit-on (app [global GR|_]) [I|_] :- I > 0,
  coq.arguments.implicit GR [Imps|_], J is I - 1, std.length Imps L, J < L, std.nth J Imps Imp,
  not (Imp = explicit), !.
sel-implicit-on T [I|P] :- kid-at T I (sel-implicit-kid P).
pred sel-implicit-kid i:list int, i:kid.
sel-implicit-kid P (kt T) :- sel-implicit-on T P.
sel-implicit-kid P (kb _ _ F) :- pi x\ sel-implicit-on (F x) P.

% [sel-before P Q] the path P comes before the path Q in pre-order
pred sel-before i:list int, i:list int.
sel-before [] [_|_].
sel-before [I|_] [J|_] :- I < J, !.
sel-before [I|P] [I|Q] :- sel-before P Q.

/* ---------------- Later instances ---------------- */

% A later instance: the path of the subterm where the outer term matches,
% and what the pattern selects there
kind sel-later type.
type sel-later list int -> sel-res -> sel-later.

% [sel-closed Bs T Rev A0 A] A is A0 with the paths of the subterms of T
% (at the reversed path Rev) that use none of the bound variables Bs nor
% one bound in T, in reverse pre-order
pred sel-closed i:list term, i:term, i:list int, i:list (list int), o:list (list int).
sel-closed Bs T Rev A A2 :-
  (std.exists Bs (occurs-in T), !, A1 = A ; std.rev Rev P, A1 = [P|A]),
  kids-fold T (sel-closed-kid Bs Rev) A1 A2.
pred sel-closed-kid i:list term, i:list int, i:term, i:int, i:kid,
                    i:list (list int), o:list (list int).
sel-closed-kid Bs Rev _ I (kt T) A A1 :- sel-closed Bs T [I|Rev] A A1.
sel-closed-kid Bs Rev _ I (kb _ _ F) A A1 :- pi x\ sel-closed [x|Bs] (F x) [I|Rev] A A1.
sel-closed-kid _ _ _ _ (kn _) A A.

% [sel-box-oracle G T P Txt R] R is what the pattern of text Txt selects
% in the scratch goal sel_box s, s being the subterm at path P of T (a
% part of the goal G), the positions written as paths of T (those outside
% s are dropped)
pred sel-box-oracle i:goal, i:term, i:list int, i:string, o:sel-res.
sel-box-oracle (goal C _ _ _ _) T P Txt R :- term-at P T S,
  sel-set-text "" "" Txt Tac, sel-scratch C S Tac "" R0, sel-box-map P R0 R1,
  sel-norm-res T R1 R.

% [sel-box-map P R R1] R1 is R, positions in sel_box s, as paths of the
% part, s being at path P
pred sel-box-map i:list int, i:sel-res, o:sel-res.
sel-box-map P (sel-ok Qs) (sel-ok Qs1) :- !, std.map-filter Qs (sel-box-pos P) Qs1.
sel-box-map _ R R.
pred sel-box-pos i:list int, i:sel-pos, o:sel-pos.
sel-box-pos P (sp-at [2|Q]) (sp-at PQ) :- std.append P Q PQ.
sel-box-pos P (sp-prefix [2|Q] K) (sp-prefix PQ K) :- std.append P Q PQ.

% [sel-later-instances G T F First Ls] Ls are the later instances, in T
% (a part of G), of the outer term of the pattern of form F whose first
% instance has the occurrences First
pred sel-later-instances i:goal, i:term, i:sel-form, i:list sel-pos, o:list sel-later.
sel-later-instances G T F First Ls :-
  std.map First sel-pos-path FPs, FPs = [F1|_],
  sel-closed [] T [] [] Ps0, std.rev Ps0 Ps,
  std.filter Ps (p\ sel-before F1 p, not (std.mem FPs p)) Cands,
  sel-outer F Outer, sel-form-text F Full,
  sel-later-scan G T Outer Full Cands Ls.

% [sel-later-scan G T Outer Full Cands Ls] Ls are the later instances
% among the candidate paths Cands: where the outer term matches at the root
pred sel-later-scan i:goal, i:term, i:string, i:string, i:list (list int), o:list sel-later.
sel-later-scan _ _ _ _ [] [].
sel-later-scan G T Outer Full [P|Ps] Ls :-
  sel-box-oracle G T P Outer RO,
  (RO = sel-ok Qs, std.mem Qs (sp-at P), !,
   sel-box-oracle G T P Full RF, Ls = [sel-later P RF|Ls1] ;
   Ls = Ls1),
  sel-later-scan G T Outer Full Ps Ls1.

/* ---------------- The algebra of selectors ---------------- */

/* ~/claudeExp/subterm-select/GRAMMAR.md.  A selector denotes a set of
   positions of a term; it is built from blocks (root, step, match, hole)
   and operators (then, pick, union, name).  The ssreflect patterns are
   some of the combinations: [t] is a match, [X in C] a hole, [t in X in
   C] a hole then a match, [t as X in C] a hole whose X part must match t
   (law 4), {k}[..] a pick.  These are denoted by the oracle (ssreflect's
   set); the other combinations by composition over the oracle's leaves
   (then reads its right selector inside each place of its left one, on
   the scratch goal sel_box s of that place). */

kind selector type.
type s-root selector.                                 % ε
type s-step int -> selector.                          % i
type s-match string -> selector.                      % ⟨p⟩, p a term pattern
type s-hole string -> string -> selector.             % ⟨C | X⟩
type s-hole-as string -> string -> string -> selector. % ⟨C[t/X] | X⟩: t, X, C
type s-then selector -> selector -> selector.         % s ; s'
type s-pick selector -> pick -> selector.             % s # K
type s-union selector -> selector -> selector.        % s ∪ s'
type s-name string -> selector.                       % a name (sel-named)

% a set of ranks (from 1, in pre-order), or its complement
kind pick type.
type pick-in list int -> pick.
type pick-out list int -> pick.

% [sel-named N S] the name N stands for the selector S
pred sel-named o:string, o:selector.
sel-named "RHS" (s-hole "_ = X" "X").
sel-named "LHS" (s-hole "X = _" "X").

% [sel-of-pat P S] S is the selector of the ssreflect pattern P
pred sel-of-pat i:sel-pat, o:selector.
sel-of-pat (sel-pat "" _ F) S :- !, sel-of-form F S.
sel-of-pat (sel-pat Occ _ F) (s-pick S K) :- sel-of-form F S, sel-pick-of-text Occ K.

pred sel-of-form i:sel-form, o:selector.
sel-of-form (sf-term T) (s-match T).
sel-of-form (sf-in X C) (s-hole C X).
sel-of-form (sf-in-in T X C) (s-then (s-hole C X) (s-match T)).
sel-of-form (sf-as-in T X C) (s-hole-as T X C).

% [sel-pick-of-text Occ K] K is the occurrence switch Occ ({1 3}, {-2})
pred sel-pick-of-text i:string, o:pick.
sel-pick-of-text Occ K :- N is size Occ - 2, S0 is substring Occ 1 N, sel-trim S0 S,
  (starts-with "-" S, !, M is size S - 1, S1 is substring S 1 M, sel-ints S1 Is, K = pick-out Is ;
   starts-with "+" S, !, M is size S - 1, S1 is substring S 1 M, sel-ints S1 Is, K = pick-in Is ;
   sel-ints S Is, K = pick-in Is).
pred sel-ints i:string, o:list int.
sel-ints S Is :- sel-trim S S1, rex.split "[ \t]+" S1 Ss,
  std.map-filter Ss (s\ i\ rex.match "^[0-9]+$" s, i is string_to_int s) Is.

% [sel-pick-text K S] S is the occurrence switch of K
pred sel-pick-text i:pick, o:string.
sel-pick-text (pick-in Is) S :- sel-ints-text Is T, S is "{" ^ T ^ "}".
sel-pick-text (pick-out Is) S :- sel-ints-text Is T, S is "{-" ^ T ^ "}".
pred sel-ints-text i:list int, o:string.
sel-ints-text Is S :- std.map Is (i\ s\ s is int_to_string i) Ss, std.string.concat " " Ss S.

% [sel-to-ssr S Occ Txt] the selector S is the ssreflect pattern Txt with
% the occurrence switch Occ ("" for none): the selectors that ssreflect
% writes as they are (step 3 flattens the others with the laws)
pred sel-to-ssr i:selector, o:string, o:string.
sel-to-ssr (s-pick S K) Occ Txt :- !, sel-to-ssr-plain S Txt, sel-pick-text K Occ.
sel-to-ssr (s-name N) Occ Txt :- sel-named N S, !, sel-to-ssr S Occ Txt.
sel-to-ssr S "" Txt :- sel-to-ssr-plain S Txt.
pred sel-to-ssr-plain i:selector, o:string.
sel-to-ssr-plain (s-match T) T.
sel-to-ssr-plain (s-hole C X) S :- S is X ^ " in " ^ C.
sel-to-ssr-plain (s-hole-as T X C) S :- S is T ^ " as " ^ X ^ " in " ^ C.
sel-to-ssr-plain (s-then (s-hole C X) (s-match T)) S :- S is T ^ " in " ^ X ^ " in " ^ C.
sel-to-ssr-plain (s-name N) S :- sel-named N Sel, sel-to-ssr-plain Sel S.

% [sel-show S T] T is the selector S written as in GRAMMAR.md
pred sel-show i:selector, o:string.
sel-show s-root "ε".
sel-show (s-step I) S :- S is int_to_string I.
sel-show (s-match T) S :- S is "⟨" ^ T ^ "⟩".
sel-show (s-hole C X) S :- S is "⟨" ^ C ^ " | " ^ X ^ "⟩".
sel-show (s-hole-as T X C) S :- S is "⟨(" ^ C ^ ")[" ^ T ^ "/" ^ X ^ "] | " ^ X ^ "⟩".
sel-show (s-then A B) S :- sel-show A SA, sel-show B SB, S is SA ^ " ; " ^ SB.
sel-show (s-pick A K) S :- sel-show A SA, sel-pick-text K KS,
  (A = s-then _ _, !, S is "(" ^ SA ^ ") # " ^ KS ; A = s-union _ _, !, S is "(" ^ SA ^ ") # " ^ KS ;
   S is SA ^ " # " ^ KS).
sel-show (s-union A B) S :- sel-show A SA, sel-show B SB, S is "(" ^ SA ^ " ∪ " ^ SB ^ ")".
sel-show (s-name N) N.

% [sel-denote G H T P S R] R is what the selector S denotes in the
% subterm at path P of T, the part H of the goal G (H = "" for the
% conclusion); the positions are paths of T.  An ssreflect pattern at the
% root of the part is the oracle on the goal itself; elsewhere, the oracle
% on the scratch goal sel_box s of the subterm s at P.
pred sel-denote i:goal, i:string, i:term, i:list int, i:selector, o:sel-res.
sel-denote G H T [] S R :- sel-to-ssr S Occ Txt, !, sel-oracle G H Occ Txt R0, sel-norm-res T R0 R.
sel-denote G _ T P S R :- sel-to-ssr S Occ Txt, !,
  (term-at P T _, !, sel-box-oracle-occ G T P Occ Txt R0, sel-norm-res T R0 R ;
   R = sel-error "the place uses a variable bound in the goal: the oracle cannot be run there").
sel-denote _ _ _ P s-root (sel-ok [sp-at P]).
sel-denote _ _ T P (s-step I) R :- std.append P [I] PI,
  (path-of T PI, !, R = sel-ok [sp-at PI] ; R = sel-ok []).
sel-denote G H T P (s-then A B) R :- sel-denote G H T P A RA,
  (RA = sel-ok Qs, !, sel-then-each G H T Qs B [] R ; R = RA).
sel-denote G H T P (s-pick A K) R :- sel-denote G H T P A RA,
  (RA = sel-ok Qs, !, sel-pick-ranks Qs K 1 Qs1, R = sel-ok Qs1 ; R = RA).
sel-denote G H T P (s-union A B) R :- sel-denote G H T P A RA, sel-denote G H T P B RB,
  (RA = sel-ok QA, RB = sel-ok QB, !, sel-merge QA QB Q, R = sel-ok Q ;
   RA = sel-error _, !, R = RA ; R = RB).
sel-denote G H T P (s-name N) R :- sel-named N S, !, sel-denote G H T P S R.
sel-denote _ _ _ _ (s-name N) (sel-error M) :- M is "unknown name " ^ N.


% [sel-norm-res T R R1] R1 is R where a prefix of an application without
% all its arguments is its head: the path P.0 (set puts z in place of a
% head as in place of a prefix: z a b)
pred sel-norm-res i:term, i:sel-res, o:sel-res.
sel-norm-res T (sel-ok Qs) (sel-ok Qs1) :- !, std.map Qs (sel-norm-pos T) Qs1.
sel-norm-res _ R R.
pred sel-norm-pos i:term, i:sel-pos, o:sel-pos.
sel-norm-pos T (sp-prefix P K) (sp-at P0) :- sel-arity-at P T N, N = K, !,
  std.append P [0] P0.
sel-norm-pos _ Q Q.

% [sel-arity-at P T N] the subterm at path P of T is an application to N
% arguments
pred sel-arity-at i:list int, i:term, o:int.
sel-arity-at [] (app [_|As]) N :- std.length As N.
sel-arity-at [I|P] T N :- kid-at T I (sel-arity-kid P N).
pred sel-arity-kid i:list int, o:int, i:kid.
sel-arity-kid P N (kt T) :- sel-arity-at P T N.
sel-arity-kid P N (kb _ _ F) :- pi x\ sel-arity-at P (F x) N.

% [sel-then-each G H T Qs B Acc R] B read inside each position of Qs
pred sel-then-each i:goal, i:string, i:term, i:list sel-pos, i:selector,
                   i:list sel-pos, o:sel-res.
sel-then-each _ _ _ [] _ Acc (sel-ok Acc).
sel-then-each G H T [sp-at Q|Qs] B Acc R :- sel-denote G H T Q B RB,
  (RB = sel-ok QB, !, sel-merge Acc QB Acc1, sel-then-each G H T Qs B Acc1 R ; R = RB).
sel-then-each _ _ _ [sp-prefix _ _|_] _ _
  (sel-error "a prefix of an application has no subterms to read a selector in").

% [sel-pick-ranks Qs K I Qs1] Qs1 are the positions of Qs (the first of
% rank I) whose rank is picked by K
pred sel-pick-ranks i:list sel-pos, i:pick, i:int, o:list sel-pos.
sel-pick-ranks [] _ _ [].
sel-pick-ranks [Q|Qs] K I Qs1 :- I1 is I + 1,
  ((K = pick-in Is, std.mem! Is I ; K = pick-out Is, not (std.mem! Is I)), !,
   Qs1 = [Q|Qs2] ; Qs1 = Qs2),
  sel-pick-ranks Qs K I1 Qs2.

% [sel-merge A B C] C is the union of the positions A and B, in pre-order
pred sel-merge i:list sel-pos, i:list sel-pos, o:list sel-pos.
sel-merge [] B B :- !.
sel-merge A [] A :- !.
sel-merge [X|A] [X|B] [X|C] :- !, sel-merge A B C.
sel-merge [X|A] [Y|B] [X|C] :- sel-pos-path X PX, sel-pos-path Y PY,
  (sel-before PX PY ; PX = PY), !, sel-merge A [Y|B] C.
sel-merge A [Y|B] [Y|C] :- sel-merge A B C.

% [sel-box-oracle-occ G T P Occ Txt R] sel-box-oracle with an occurrence
% switch
pred sel-box-oracle-occ i:goal, i:term, i:list int, i:string, i:string, o:sel-res.
sel-box-oracle-occ (goal C _ _ _ _) T P Occ Txt R :- term-at P T S,
  sel-set-text "" Occ Txt Tac, sel-scratch C S Tac "" R0, sel-box-map P R0 R.

/* ---------------- The report ---------------- */

% [sel-part G H T] T is the part of G where the pattern is looked for:
% the conclusion (H = "") or the type of the hypothesis H
pred sel-part i:goal, i:string, o:term.
sel-part (goal _ _ Ty _ _) "" Ty :- !.
sel-part (goal Ctx _ _ _ _) H T :-
  (std.mem Ctx (decl _ N T) ; std.mem Ctx (def _ N _ T)), coq.name->id N H, !.
sel-part _ H _ :- coq.ltac.fail 0 {msg "no hypothesis"} H.

% [sel-select G H S Pat R] R is what the pattern of text S selects in the
% part H of G, Pat the pattern read
pred sel-select i:goal, i:string, i:string, o:sel-pat, o:sel-res.
sel-select G H S Pat R :- sel-parse S Pat, sel-of-pat Pat Sel, sel-part G H T,
  sel-denote G H T [] Sel R.

% [sel-cast-at P T] the subterm at path P of T is a cast
pred sel-cast-at i:list int, i:term.
sel-cast-at [] (let N _ _ F) :- cast-let N F.
sel-cast-at [I|P] T :- kid-at T I (sel-cast-kid P).
pred sel-cast-kid i:list int, i:kid.
sel-cast-kid P (kt T) :- sel-cast-at P T.
sel-cast-kid P (kb _ _ F) :- pi x\ sel-cast-at P (F x).

% [sel-pos-line T Q L] L describes the position Q of T
pred sel-pos-line i:term, i:sel-pos, o:string.
sel-pos-line T Q L :- sel-pos-string Q PS, sel-pos-text T Q Txt,
  sel-pos-path Q P,
  (sel-hidden T P, !, Fl0 = "  (not printed)" ; Fl0 = ""),
  (sel-cast-at P T, !, Fl is Fl0 ^ "  (a cast, that set erases: the selection may be its term, at .1)" ; Fl = Fl0),
  (Q = sp-prefix _ K, !,
   Pr is "  (a prefix of the application, without its last " ^ {std.any->string K} ^ " argument(s))" ;
   Pr = ""),
  L is "  " ^ PS ^ "  " ^ Txt ^ Fl ^ Pr.

% [sel-count-line N L] L says how many positions are selected
pred sel-count-line i:int, o:string.
sel-count-line 0 "nothing selected" :- !.
sel-count-line 1 "univocal" :- !.
sel-count-line N L :- L is {std.any->string N} ^ " positions".

% [sel-later-line T L S] S describes the later instance L
pred sel-later-line i:term, i:sel-later, o:string.
sel-later-line T (sel-later P R) S :- string-of-path P PS, text-at P T Txt,
  (R = sel-ok [], !, W = "selects nothing there" ;
   R = sel-ok Qs, !, sel-positions-string Qs QS, W is "would select " ^ QS ;
   R = sel-error M, W is "the pattern fails there: " ^ M),
  S is "  at " ^ PS ^ "  " ^ Txt ^ ": " ^ W.

% [sel-report G H S] prints what the pattern of text S selects in the
% part H of the goal G, and its later instances
pred sel-report i:goal, i:string, i:string.
sel-report G H S :- sel-part G H T, sel-select G H S Pat R,
  Pat = sel-pat Occ Txt F, sel-form-kind F K, sel-kind-label K KL,
  (Occ = "", !, KS = KL ; KS is KL ^ ", " ^ {sel-kind-label e1-occurrence-switch}),
  (H = "", !, Where = "the conclusion" ; Where is "the type of " ^ H),
  sel-of-pat Pat Sel, sel-show Sel SS,
  Head is "pattern " ^ Occ ^ "[" ^ Txt ^ "] (" ^ KS ^ "; " ^ SS ^ ") in " ^ Where ^ ":",
  (R = sel-error M, !, Out is Head ^ "\n  ssreflect refuses it: " ^ M, coq.say Out ;
   R = sel-ok Qs, std.map Qs (sel-pos-line T) Ls, std.length Qs N,
   sel-count-line N CL,
   (Qs = [], !, LL = [] ;
    sel-later-instances G T F Qs Lt, std.map Lt (sel-later-line T) LL0,
    (LL0 = [], !, LL = ["no later instance"] ;
     LL = ["later instances (fragility):"|LL0])),
   std.flatten [[Head], Ls, [CL], LL] All, std.string.concat "\n" All Out,
   coq.say Out).

% [sel-positions-string Qs S] S are the positions Qs, separated by blanks
pred sel-positions-string i:list sel-pos, o:string.
sel-positions-string Qs S :- std.map Qs sel-pos-string Ss, std.string.concat " " Ss S.

% [sel-norm-expect S N] N is the expected positions S, one blank between
pred sel-norm-expect i:string, o:string.
sel-norm-expect S N :- sel-trim S S1, rex.replace "[ \t\n]+" " " S1 N.

% [sel-args K Args H S Rest] the arguments Args are an optional hypothesis
% H ("" when there is none), the pattern S, then the K strings Rest
pred sel-args i:int, i:list argument, o:string, o:string, o:list string.
sel-args K Args H S Rest :- std.map Args (a\ s\ a = str s) Ss, !,
  std.length Ss N,
  (N is K + 1, !, H = "", Ss = [S|Rest] ;
   N is K + 2, !, Ss = [H, S|Rest] ;
   coq.ltac.fail 0 {msg "wrong number of arguments"}).
sel-args _ _ _ _ _ :- coq.ltac.fail 0 {msg "the arguments are strings"}.

/* ---------------- select_all: the ways to designate a position ---------------- */

/* Given the path p of a subterm of a part T, the candidates are built,
   one or more per kind, each one CHECKED by the oracle (sel-select): it is
   kept when it denotes exactly {p}, or, marked "selects also", when it
   denotes p and other positions (a kind that can only give the whole set
   of occurrences of an instance).  Then they are sorted by sg-cost.

   Generalization (anti-unification).  A term pattern for a subterm t of
   the part must match t and no subterm before t (pre-order) that has the
   same key (head constant): those are its competitors.  For each
   competitor c, the disagreement positions of t and c are the highest
   positions where they differ (a different head, or a different leaf);
   a pattern that keeps t at one of them (or keeps the node above it, or a
   subterm below which it lies) does not match c.  The pattern keeps a set
   K of such positions, the nodes above them (their heads) and the head of
   t: K is a smallest hitting set of the disagreement sets, the size being
   the symbols kept; the search is exact when there are at most
   sg-exact-bound positions in all, greedy beyond (the output says which).
   Only printed positions are kept (not an implicit argument: it is a hole,
   which elaboration fills).

   Kinds (sel-kind):
   - B (term pattern): the generalization of the target t;
   - C1 [X in C]: for an ancestor A of the target, the generalization of A
     with X at the target (competitors: the subterms before A with A's
     key; the disagreements inside the X part do not count);
   - C2 [t in X in C]: an ancestor m of the target is the X part of a
     context from an ancestor A of m; t is the generalization of the target
     against the competitors inside m before it;
   - C3 [t as X in C]: the generalization of an ancestor A, the target
     included, cut at the target: C with X there, t the part at X;
   - E1 {k}: a candidate that selects also, with the rank k of p among its
     positions; A2 {k}t: the target written in full, with its rank;
   - A1: the path itself.
   Not generated (ssreflect refuses them or reads them otherwise, see the
   round trip of subterm_select_test.v): [X in X]; X at the head of an
   application; X under a binder of the context (X would be applied to
   bound variables, which set reads up to eta).  A target that only these
   could designate has no ssreflect form: then only E1/A2/A1 remain. */

% the kinds of candidates, with their text and its context depth
kind sg-cand type.
type sg-cand sel-kind -> string -> int -> string -> sg-cand. % kind, text, depth, note

% [sg-exact-bound N] the hitting set is searched exactly up to N positions
pred sg-exact-bound o:int.
sg-exact-bound 10.

% [sg-cost K Txt Depth Ok C] C is the cost of the candidate of kind K, text
% Txt, context depth Depth (Ok: it denotes exactly the target), compared
% lexicographically: occurrence number or path (big), not exact (big),
% kept symbols, context depth, type annotations (none are written), text
% length.  Provisional: the one place to change it.
pred sg-cost i:sel-kind, i:string, i:int, i:bool, o:list int.
sg-cost K Txt D Ok [O, E, S, D, 0, L] :-
  (K = e1-occurrence-switch, !, O = 1000 ; K = a2-occurrence, !, O = 1000 ;
   K = a1-path, !, O = 2000 ; O = 0),
  (Ok = tt, !, E = 0 ; E = 1000),
  sg-symbols Txt S, L is size Txt.

% [sg-symbols Txt N] N is the number of symbols that the pattern Txt keeps:
% its tokens other than the holes, X, the keywords in and as, the brackets
% and the occurrence switch
pred sg-symbols i:string, o:int.
sg-symbols Txt N :-
  sel-parse Txt (sel-pat _ T _),
  rex.replace "\\([][(){},;]\\)" " \\1 " T T1,
  rex.split "[ \t\n]+" T1 Ts,
  std.filter Ts (t\ not (std.mem! ["", "_", "X", "in", "as", "(", ")", "[", "]", "{", "}"] t)) Ks,
  std.length Ks N.

% [sg-less A B] the cost A is less than B (lexicographic)
pred sg-less i:list int, i:list int.
sg-less [X|_] [Y|_] :- X < Y, !.
sg-less [X|A] [X|B] :- sg-less A B.

% a checked candidate: its cost, kind, text, note, and what it selects
kind sg-res type.
type sg-res list int -> sel-kind -> string -> string -> list sel-pos -> sg-res.

pred sg-insert i:sg-res, i:list sg-res, o:list sg-res.
sg-insert R [] [R].
sg-insert (sg-res C _ _ _ _ as R) [(sg-res C1 _ _ _ _ as R1)|Rs] [R, R1|Rs] :- sg-less C C1, !.
sg-insert R [R1|Rs] [R1|Rs1] :- sg-insert R Rs Rs1.

pred sg-sort i:list sg-res, o:list sg-res.
sg-sort L S :- std.fold L [] sg-insert S.

/* ---- subterms, keys, disagreements ---- */

% [sg-key T K] K is the key of T: its head constant
pred sg-key i:term, o:term.
sg-key (app [global G|_]) (global G) :- !.
sg-key (app [pglobal G _|_]) (global G) :- !.
sg-key (app [H|_]) H :- name H, (decl H _ _ ; def H _ _ _), !.

% [sg-competitors T P Ks Cs] Cs are the subterms of T before the path P in
% pre-order (P's ancestors included), closed, with the key Ks
pred sg-competitors i:term, i:list int, i:term, o:list term.
sg-competitors T P K Cs :-
  sel-closed [] T [] [] Ps0, std.rev Ps0 Ps,
  std.filter Ps (q\ sel-before q P) Before,
  std.map-filter Before (q\ c\ term-at q T c, sg-key c K) Cs.

% [sg-within T M P Ks Cs] the competitors inside the subterm at path M of
% T, before the target at P (paths relative to M are not needed)
pred sg-within i:term, i:list int, i:list int, i:term, o:list term.
sg-within T M P K Cs :-
  sel-closed [] T [] [] Ps0, std.rev Ps0 Ps,
  std.filter Ps (q\ sel-prefix-of M q, sel-before q P) Before,
  std.map-filter Before (q\ c\ term-at q T c, sg-key c K) Cs.

% [sel-prefix-of P Q] the path P is a prefix of Q
pred sel-prefix-of i:list int, i:list int.
sel-prefix-of [] _.
sel-prefix-of [I|P] [I|Q] :- sel-prefix-of P Q.

% [sg-related P Q] one of the paths P, Q is a prefix of the other
pred sg-related i:list int, i:list int.
sg-related P Q :- sel-prefix-of P Q, !.
sg-related P Q :- sel-prefix-of Q P.

% [sg-diff T C Rev Ds0 Ds] Ds is Ds0 with the disagreement positions of T
% and C (Rev: the reversed position of T)
pred sg-diff i:term, i:term, i:list int, i:list (list int), o:list (list int).
sg-diff T C _ Ds Ds :- same_term T C, !.
sg-diff (app [H|As]) (app [H1|Bs]) Rev Ds0 Ds :- same_term H H1,
  std.length As N, std.length Bs N, !, sg-diff-args As Bs Rev 1 Ds0 Ds.
sg-diff _ _ Rev Ds [P|Ds] :- std.rev Rev P.
pred sg-diff-args i:list term, i:list term, i:list int, i:int, i:list (list int), o:list (list int).
sg-diff-args [] [] _ _ Ds Ds.
sg-diff-args [A|As] [B|Bs] Rev I Ds0 Ds :-
  sg-diff A B [I|Rev] Ds0 Ds1, I1 is I + 1, sg-diff-args As Bs Rev I1 Ds1 Ds.

/* ---- the generalization ---- */

% A region: none, or the X part at a relative path, wild (C1, C2: the
% disagreements inside it do not count) or full (C3)
kind sg-region type.
type sg-none sg-region.
type sg-wild list int -> sg-region.
type sg-full list int -> sg-region.

% [sg-dsets T R Cs Dss] Dss are the disagreement sets that a pattern of T
% (region R) must hit, one per competitor of Cs that it does not exclude
% anyway; it fails if a competitor cannot be excluded
pred sg-dsets i:term, i:sg-region, i:list term, o:list (list (list int)).
sg-dsets _ _ [] [].
sg-dsets T R [C|Cs] Dss :- sg-diff T C [] [] Ds0,
  std.filter Ds0 (d\ not (sel-hidden T d)) Ds1,
  (R = sg-wild Q, !, std.filter Ds1 (d\ not (sel-prefix-of Q d)) Ds2,
   (std.exists Ds2 (d\ sel-prefix-of d Q, not (d = Q)), !, Excl = tt ; Excl = ff) ;
   R = sg-full Q, !, Ds2 = Ds1,
   (std.exists Ds2 (d\ sel-prefix-of d Q), !, Excl = tt ; Excl = ff) ;
   Ds2 = Ds1, Excl = ff),
  (Excl = tt, !, Dss = Dss1 ;
   Ds0 = [], !, Dss = Dss1 ;  % the same term: an occurrence of the same instance
   Ds2 = [_|_], Dss = [Ds2|Dss1]),
  sg-dsets T R Cs Dss1.

% [sg-covers K Ds] the kept positions K hit the disagreement set Ds
pred sg-covers i:list (list int), i:list (list int).
sg-covers K Ds :- std.exists Ds (d\ std.exists K (k\ sg-related d k)), !.

% [sg-hitting T R Dss K How] K is a smallest set of positions hitting
% the disagreement sets Dss (size: sg-kept-size), How says how it was found
pred sg-hitting i:term, i:sg-region, i:list (list (list int)), o:list (list int), o:string.
sg-hitting _ _ [] [] "no competitor left" :- !.
sg-hitting T R Dss K How :- std.flatten Dss U0, sg-undup U0 U, std.length U N,
  sg-exact-bound B,
  (N =< B, !, How = "exact search",
   sg-subsets U Ss,
   std.filter Ss (k\ std.forall Dss (sg-covers k)) Ok,
   std.map Ok (k\ p\ sigma S\ sg-kept-size T R k S, p = pr S k) Sized,
   sg-min Sized (pr _ K) ;
   How = "greedy", sg-greedy Dss [] K).

% [sg-undup L L1] L1 is L without its repetitions
pred sg-undup i:list A, o:list A.
sg-undup [] [].
sg-undup [X|L] L1 :- std.mem! L X, !, sg-undup L L1.
sg-undup [X|L] [X|L1] :- sg-undup L L1.

pred sg-subsets i:list A, o:list (list A).
sg-subsets [] [[]].
sg-subsets [X|Xs] Ss :- sg-subsets Xs S1, std.map S1 (s\ t\ t = [X|s]) S2, std.append S1 S2 Ss.

pred sg-min i:list (pair int (list (list int))), o:pair int (list (list int)).
sg-min [P] P :- !.
sg-min [pr S K|Ps] M :- sg-min Ps (pr S1 K1), (S =< S1, !, M = pr S K ; M = pr S1 K1).

% [sg-greedy Dss K0 K] K: K0 and, while a set is not hit, the position
% hitting the most sets
pred sg-greedy i:list (list (list int)), i:list (list int), o:list (list int).
sg-greedy Dss K K :- std.forall Dss (sg-covers K), !.
sg-greedy Dss K0 K :-
  std.filter Dss (ds\ not (sg-covers K0 ds)) Left, std.flatten Left U0, sg-undup U0 U,
  std.map U (u\ p\ sigma N L\ std.filter Left (ds\ sg-covers [u] ds) L, std.length L N, p = pr N u) Ns,
  sg-max Ns (pr _ Best), sg-greedy Dss [Best|K0] K.
pred sg-max i:list (pair int (list int)), o:pair int (list int).
sg-max [P] P :- !.
sg-max [pr N U|Ps] M :- sg-max Ps (pr N1 U1), (N >= N1, !, M = pr N U ; M = pr N1 U1).

% [sg-node-kept Pos K R] the node at Pos is kept (its head): the root, or
% above a kept position or the region
pred sg-node-kept i:list int, i:list (list int), i:sg-region.
sg-node-kept [] _ _ :- !.
sg-node-kept Pos K _ :- std.exists K (k\ sel-prefix-of Pos k, not (Pos = k)), !.
sg-node-kept Pos _ (sg-wild Q) :- sel-prefix-of Pos Q, not (Pos = Q), !.
sg-node-kept Pos _ (sg-full Q) :- sel-prefix-of Pos Q, !.

% [sg-build T Rev K R X P] P is the pattern of T (at the reversed relative
% position Rev) that keeps K, with X at the wild region of R
pred sg-build i:term, i:list int, i:list (list int), i:sg-region, i:term, o:term.
sg-build T Rev K R X P :- std.rev Rev Pos,
  (R = sg-wild Pos, !, P = X ;
   std.mem! K Pos, !, P = T ;
   sg-node-kept Pos K R, !, sg-build-node T Rev K R X P ;
   P = {{ @pbp_hole Prop lp:T }}).
pred sg-build-node i:term, i:list int, i:list (list int), i:sg-region, i:term, o:term.
sg-build-node (app [H|As]) Rev K R X (app [H|Ps]) :- !, sg-build-args As Rev 1 K R X Ps.
sg-build-node T _ _ _ _ T.
pred sg-build-args i:list term, i:list int, i:int, i:list (list int), i:sg-region, i:term, o:list term.
sg-build-args [] _ _ _ _ _ [].
sg-build-args [A|As] Rev I K R X [P|Ps] :-
  sg-build A [I|Rev] K R X P, I1 is I + 1, sg-build-args As Rev I1 K R X Ps.

% [sg-kept-size T R K S] S is the number of symbols that the pattern of T
% keeping K keeps (the printed ones)
pred sg-kept-size i:term, i:sg-region, i:list (list int), o:int.
sg-kept-size T R K S :- sg-build T [] K R {{ True }} P, sg-size P S.
pred sg-size i:term, o:int.
sg-size {{ @pbp_hole _ _ }} 0 :- !.
sg-size (app [global G|As]) S :- !,
  (coq.arguments.implicit G [Imps|_] ; Imps = []), !,
  sg-size-args As Imps 0 S0, S is S0 + 1.
sg-size (app [H|As]) S :- !, sg-size H S1, sg-size-args As [] 0 S0, S is S0 + S1.
sg-size _ 1.
pred sg-size-args i:list term, i:list implicit_kind, i:int, o:int.
sg-size-args [] _ S S.
sg-size-args [_|As] [I|Is] S0 S :- not (I = explicit), !, sg-size-args As Is S0 S.
sg-size-args [A|As] Is S0 S :- sg-size A S1, S2 is S0 + S1,
  (Is = [_|Is1], ! ; Is1 = []), sg-size-args As Is1 S2 S.

% [sg-print P S] S is the text of the pattern P (holes printed _)
pred sg-print i:term, o:string.
sg-print P S :- default-printing (coq.term->string P S0),
  rex.replace "\\bpbp_hole\\b" "_" S0 S1, one-line S1 S.

% [sg-print-ctx Ty TA K R S] S is the text of the context: the pattern of
% TA keeping K, with X (of type Ty) at the relative path R
pred sg-print-ctx i:term, i:term, i:list (list int), i:list int, o:string.
sg-print-ctx Ty TA K R S :- coq.id->name "X" N,
  pi x\ sigma Pat\ decl x N Ty => (sg-build TA [] K (sg-wild R) x Pat, sg-print Pat S).

/* ---- the candidates ---- */

% [sg-take N L L1] L1 is the first N elements of L (all of L if shorter)
pred sg-take i:int, i:list A, o:list A.
sg-take 0 _ [] :- !.
sg-take _ [] [] :- !.
sg-take N [X|L] [X|L1] :- N1 is N - 1, sg-take N1 L L1.

% [sg-ancestors P As] As are the strict ancestors of the path P, the
% nearest first
pred sg-ancestors i:list int, o:list (list int).
sg-ancestors [] [] :- !.
sg-ancestors P [Q|Qs] :- parent P Q, sg-ancestors Q Qs.

% [sg-plain-chain T A R] from the subterm A of T, the path R goes down
% through arguments of applications only (no binder, no head)
pred sg-plain-chain i:term, i:list int.
sg-plain-chain _ [].
sg-plain-chain (app L) [I|R] :- I > 0, std.length L N, I < N, std.nth I L T,
  not (sel-hidden (app L) [I]), sg-plain-chain T R.

% [sg-drop Q P R] the path P is Q then R
pred sg-drop i:list int, i:list int, o:list int.
sg-drop [] R R.
sg-drop [I|Q] [I|P] R :- sg-drop Q P R.

% [sg-term-cand T P C] C is the term pattern (B) of the target at P of T
pred sg-term-cand i:term, i:list int, o:sg-cand.
sg-term-cand T P C :- term-at P T Tt,
  (sg-key Tt K, !, sg-competitors T P K Cs, sg-dsets Tt sg-none Cs Dss,
   sg-hitting Tt sg-none Dss Kp How, sg-build Tt [] Kp sg-none {{ True }} Pat,
   sg-print Pat S, sel-form-kind (sf-term S) Kd, C = sg-cand Kd S 0 How ;
   sg-print Tt S, C = sg-cand b1-closed-term S 0 "no key").

% [sg-context-cands T P Cs] the C1 candidates [X in C] of the target at P
pred sg-context-cands i:term, i:list int, o:list sg-cand.
sg-context-cands T P Cs :- sg-ancestors P As, sg-take 6 As As1,
  std.map-filter As1 (a\ c\ sg-c1 T P a c) Cs.
pred sg-c1 i:term, i:list int, i:list int, o:sg-cand.
sg-c1 T P A (sg-cand c1-context S D How) :-
  term-at A T TA, sg-drop A P R, sg-plain-chain TA R, sg-key TA K, term-at P T Tt,
  sg-competitors T A K Cs, sg-dsets TA (sg-wild R) Cs Dss,
  sg-hitting TA (sg-wild R) Dss Kp How,
  coq.typecheck Tt Ty ok,
  sg-print-ctx Ty TA Kp R C0,
  S is "X in " ^ C0, std.length R D.

% [sg-c2-cands T P Cs] the C2 candidates [t in X in C]: X at an ancestor
% M of the target, C from an ancestor of M
pred sg-c2-cands i:term, i:list int, o:list sg-cand.
sg-c2-cands T P Cs :- term-at P T Tt, sg-key Tt Kt, !,
  sg-ancestors P Ms0, sg-take 3 Ms0 Ms,
  std.map Ms (m\ cs\ sigma As0 As\ sg-ancestors m As0, sg-take 2 As0 As,
     std.map-filter As (a\ c\ sg-c2 T P Tt Kt m a c) cs) Css,
  std.flatten Css Cs.
sg-c2-cands _ _ [].
pred sg-c2 i:term, i:list int, i:term, i:term, i:list int, i:list int, o:sg-cand.
sg-c2 T P Tt Kt M A (sg-cand c2-redex-in-context S D How) :-
  term-at A T TA, term-at M T TM, sg-drop A M R, sg-plain-chain TA R, sg-key TA K,
  sg-competitors T A K Cs, sg-dsets TA (sg-wild R) Cs Dss,
  sg-hitting TA (sg-wild R) Dss Kp How1,
  coq.typecheck TM Ty ok,
  sg-print-ctx Ty TA Kp R C0,
  sg-within T M P Kt Ct, sg-dsets Tt sg-none Ct Dt, sg-hitting Tt sg-none Dt Kt1 How2,
  sg-build Tt [] Kt1 sg-none {{ True }} PatT, sg-print PatT St,
  S is St ^ " in X in " ^ C0, std.length R D,
  How is How1 ^ ", " ^ How2.

% [sg-c3-cands T P Cs] the C3 candidates [t as X in C]
pred sg-c3-cands i:term, i:list int, o:list sg-cand.
sg-c3-cands T P Cs :- sg-ancestors P As, sg-take 6 As As1,
  std.map-filter As1 (a\ c\ sg-c3 T P a c) Cs.
pred sg-c3 i:term, i:list int, i:list int, o:sg-cand.
sg-c3 T P A (sg-cand c3-redex-as-context S D How) :-
  term-at A T TA, sg-drop A P R, sg-plain-chain TA R, sg-key TA K, term-at P T Tt,
  sg-key Tt _,
  sg-competitors T A K Cs, sg-dsets TA (sg-full R) Cs Dss,
  sg-hitting TA (sg-full R) Dss Kp How,
  std.filter Kp (k\ not (sel-prefix-of R k)) Kc,
  std.map-filter Kp (k\ r\ sg-drop R k r) Kt,
  coq.typecheck Tt Ty ok,
  sg-print-ctx Ty TA Kc R C0,
  sg-build Tt [] Kt sg-none {{ True }} PatT, sg-print PatT St,
  S is St ^ " as X in " ^ C0, std.length R D.

% [sg-candidates T P Cs] all the candidates for the target at P of T
% (before the occurrence switches)
pred sg-candidates i:term, i:list int, o:list sg-cand.
sg-candidates T P Cs :-
  (term-at P T _, sg-term-cand T P B, !, Bs = [B] ; Bs = []),
  sg-context-cands T P C1s, sg-c2-cands T P C2s, sg-c3-cands T P C3s,
  std.flatten [Bs, C1s, C2s, C3s] Cs.

/* ---- checking ---- */

% [sg-check G H P C Rs0 Rs] Rs is Rs0 with the candidate C checked: it
% denotes exactly {P}, or P and others (then also its {k} form); dropped
% otherwise
pred sg-check i:goal, i:string, i:list int, i:sg-cand, i:list sg-res, o:list sg-res.
sg-check G H P (sg-cand K S D N) Rs0 Rs :- sel-select G H S _ R,
  (R = sel-ok [sp-at P], !, sg-cost K S D tt C, Rs = [sg-res C K S N [sp-at P]|Rs0] ;
   R = sel-ok Qs, sg-rank Qs (sp-at P) 1 Rk, !,
   sg-cost K S D ff C, R1 = sg-res C K S N Qs,
   Occ is "{" ^ int_to_string Rk ^ "}", SO is Occ ^ "[" ^ S ^ "]",
   (sel-select G H SO _ (sel-ok [sp-at P]), !,
    sg-cost e1-occurrence-switch SO D tt CO,
    Rs = [sg-res CO e1-occurrence-switch SO N [sp-at P], R1|Rs0] ;
    Rs = [R1|Rs0]) ;
   Rs = Rs0).

% [sg-rank Qs Q I K] Q is the K-th of Qs (the first being the I-th)
pred sg-rank i:list sel-pos, i:sel-pos, i:int, o:int.
sg-rank [Q|_] Q I I :- !.
sg-rank [_|Qs] Q I K :- I1 is I + 1, sg-rank Qs Q I1 K.

% [sg-select-all G H P Rs] Rs are the checked ways to designate the
% position P of the part H of G, best first
pred sg-select-all i:goal, i:string, i:list int, o:list sg-res.
sg-select-all G H P Rs :- sel-part G H T,
  (path-of T P, ! ; coq.ltac.fail 0 {msg "not a path of the part:"} {string-of-path P}),
  sg-candidates T P Cs,
  std.fold Cs [] (sg-check G H P) Rs0,
  (term-at P T Tt, sg-print Tt St, sg-occurrence-cand G H T P St Ra, !, Rs1 = [Ra|Rs0] ; Rs1 = Rs0),
  string-of-path P PS, sg-cost a1-path PS 0 tt CP,
  sg-sort [sg-res CP a1-path PS "" [sp-at P]|Rs1] Rs.

% [sg-occurrence-cand G H T P St R] A2: the target written in full, St,
% with its rank among the occurrences
pred sg-occurrence-cand i:goal, i:string, i:term, i:list int, i:string, o:sg-res.
sg-occurrence-cand G H _ P St R :- sel-select G H St _ (sel-ok Qs), sg-rank Qs (sp-at P) 1 Rk,
  Occ is "{" ^ int_to_string Rk ^ "}", SO is Occ ^ "(" ^ St ^ ")",
  sel-select G H SO _ (sel-ok [sp-at P]), sg-cost a2-occurrence SO 0 tt C,
  R = sg-res C a2-occurrence SO "" [sp-at P].

% [sg-res-line R L] L describes the checked candidate R
pred sg-res-line i:sg-res, o:string.
sg-res-line (sg-res C K S N Qs) L :- sel-kind-label K KL,
  std.map C (i\ s\ s is int_to_string i) CSs, std.string.concat "," CSs CS,
  (Qs = [_], !, W = "" ; sel-positions-string Qs QS, W is "  selects also: " ^ QS),
  (N = "", !, NS = "" ; NS is "  (" ^ N ^ ")"),
  (K = a1-path, !, Txt is "\"" ^ S ^ "\"" ;
   rex.match "^{" S, !, Txt = S ; Txt is "[" ^ S ^ "]"),
  L is "  " ^ Txt ^ "   " ^ KL ^ "   cost [" ^ CS ^ "]" ^ NS ^ W.

% [sg-best Rs B] B is the best candidate that denotes exactly the target
pred sg-best i:list sg-res, o:sg-res.
sg-best [(sg-res _ _ _ _ [_] as B)|_] B :- !.
sg-best [_|Rs] B :- sg-best Rs B.

}}.

Elpi Tactic pattern_select.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "pattern_select" => (sel-args 0 Args H S [], sel-report G H S).
}}.

Elpi Tactic pattern_select_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "pattern_select_expect" => (
  sel-args 1 Args H S [Exp0], sel-norm-expect Exp0 Exp,
  sel-select G H S _ R,
  (R = sel-error M, !, coq.ltac.fail 0 {msg "ssreflect refuses"} S ":" M ;
   R = sel-ok Qs, sel-positions-string Qs Got,
   (Got = Exp, ! ; coq.ltac.fail 0 {msg S} ": got" Got "expected" Exp))).
}}.

Elpi Tactic pattern_select_later_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "pattern_select_later_expect" => (
  sel-args 1 Args H S [Exp0], sel-norm-expect Exp0 Exp,
  sel-part G H T, sel-select G H S (sel-pat _ _ F) R,
  (R = sel-ok Qs, Qs = [_|_], ! ; coq.ltac.fail 0 {msg "nothing selected by"} S),
  sel-later-instances G T F Qs Ls,
  std.map Ls (l\ s\ sigma R1 Q1\ l = sel-later _ R1,
     (R1 = sel-ok Q1, !, sel-positions-string Q1 s ; s = "error")) Gs,
  std.string.concat " | " Gs Got,
  (Got = Exp, ! ; coq.ltac.fail 0 {msg S} ": got" Got "expected" Exp)).
}}.

Elpi Tactic pattern_select_fails.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "pattern_select_fails" => (
  sel-args 0 Args H S [], sel-select G H S _ R,
  (R = sel-error _, ! ; coq.ltac.fail 0 {msg "ssreflect accepts"} S)).
}}.

(* [elpi select_all "P"] and [elpi select_all "H" "P"]: the ways to
   designate the subterm at path P (of the conclusion, or of the type of
   H), each one checked by the oracle, best first, with its cost (sg-cost)
   and how its generalization was found; "selects also" marks a candidate
   that denotes P and other positions.  [elpi select_all_expect ["H"] "P"
   "<best>"] fails unless the best one is <best>; [elpi select_all_vs ["H"]
   "P" "<pattern>"] prints the best one and the given pattern (the paper's)
   with their costs, and fails unless the pattern denotes exactly P and the
   best one keeps no more symbols (the context depth of the given pattern
   is not computed: it is shown as 0). *)

Elpi Tactic select_all.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "select_all" => (
  sel-args 0 Args H PS [], path-of-string PS P, sel-part G H T,
  sg-select-all G H P Rs, std.map Rs sg-res-line Ls,
  sel-pos-string (sp-at P) PS1, sel-pos-text T (sp-at P) Txt,
  Head is "select_all " ^ PS1 ^ " (" ^ Txt ^ "), best first:",
  std.string.concat "\n" [Head|Ls] Out, coq.say Out).
}}.

Elpi Tactic select_all_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "select_all_expect" => (
  sel-args 1 Args H PS [Exp], path-of-string PS P,
  sg-select-all G H P Rs, sg-best Rs (sg-res _ _ Best _ _),
  (Best = Exp, ! ; coq.ltac.fail 0 {msg "best"} Best "expected" Exp)).
}}.

Elpi Tactic select_all_vs.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "select_all_vs" => (
  sel-args 1 Args H PS [Pat], path-of-string PS P,
  sg-select-all G H P Rs, sg-best Rs (sg-res CB KB Best _ _),
  sel-select G H Pat (sel-pat Occ Txt F) R,
  (R = sel-ok [sp-at P], ! ; coq.ltac.fail 0 {msg "the pattern does not denote exactly the path:"} Pat),
  (Occ = "", !, sel-form-kind F K ; K = e1-occurrence-switch),
  sg-cost K Pat 0 tt CP,
  sg-res-line (sg-res CB KB Best "" [sp-at P]) LB, sg-res-line (sg-res CP K Txt "" [sp-at P]) LP,
  coq.say "ours: " LB "\npaper's:" LP,
  sg-take 3 CP CP3, sg-take 3 CB CB3,
  (not (sg-less CP3 CB3), ! ; coq.ltac.fail 0 {msg "the given pattern costs less:"} Pat),
  true).
}}.
