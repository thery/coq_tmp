(* The algebra of selectors: denotation, laws, translation to ssreflect,
   robustness (~/claudeExp/subterm-select/GRAMMAR.md).

   This file uses the type [selector] of subterm_select.v (s-root, s-step,
   s-match, s-hole, s-hole-as, s-then, s-pick, s-union, s-name) and its
   semantics (the Elpi reimplementation of ssreflect's matching, on the
   goal or on a place s alone) for the ssreflect-shaped leaves; everything
   else is composed here.

   Concrete syntax (sel-parse below).  Operators, from the loosest:
     s ++ s'          union                      (also written ∪)
     s ; s'           then: s' read inside each place s gives (also ".")
     s # K            pick: K is  k  or  {k1 k2 ..}  or  {-k1 ..}  or  -k
   Atoms:
     root             ε, the whole part                (also written ε)
     i                step i (app: head 0, args 1 ..); "2.3.1" = 2 ; 3 ; 1
     <p>              match: the occurrences of the first instance of p
     <C | X>          hole: the X parts of the occurrences of the first C
     <C | X := t>     the hole with the redex put in, ⟨C[t/X] | X⟩ (C3)
     [pattern]        any ssreflect pattern, read as its selector
                      ([t in X in C] is <C | X> ; <t>, {k}[..] a pick)
     N                a name: RHS, LHS, or one made by  Elpi sel_define "N" "s".
     ( s )            grouping
   ⟨ ⟩ may be used for < >.  Inside < >, a > closes the brackets unless it
   is part of -> or => or inside parentheses; | splits C from X at the
   bracket depth 0 (|| is not a split).

   Denotation (alg-denote).  root and steps are paths; a leaf (match,
   hole, hole with redex) is the semantics at the place reached (paths
   relative to that place, given back as paths of the part); then, pick
   and union compose.  A part that fails (ssreflect refuses it) makes the
   whole selector fail.  The pick counts ranks in pre-order among the
   positions denoted ({k} beyond them selects nothing; ssreflect would
   refuse it).

   Laws (sel-normalize).  On the goal at hand:
   - law 1: the then-chains are flattened, the roots dropped;
   - law 4: <C | X := _> is <C | X>; an `as' is kept as one hole with its
     redex put in (s-hole-as): it is matched in one step, no side condition;
   - law 5: (s # K) # K' is s # K'∘K (ranks of ranks, also for the
     complements {-..}); s # K is s when K keeps all the positions of s at
     every place where it is read; # {-} is dropped;
   - law 3: <C1 | X> ; <C2 | Y> becomes <C1[C2/X] | Y> (and likewise with
     a redex at Y) only when, at every place where it is read, the X part
     of the first instance of C1 IS an instance of C2 (checked with the
     semantics: C2, its holes as _, selects the root of
     that X part), and the two denotations are checked equal there.  Note:
     GRAMMAR.md says "has an instance of C2 in its X part"; that is not
     enough: in f a (h (g 1)) + f b (g 2) = 0, <f _ X | X> ; <g Y | Y>
     gives 1 and <f _ (g Y) | Y> gives 2 (test file).

   ssreflect form (alg-to-ssr).  The normal form is written as t, X in C,
   t as X in C, t in X in C, each possibly under {K}, when it has one of
   these shapes; else, when the positions are the occurrences of one term,
   as {k..}(that term) (A2/E1, with a warning: it no longer describes the
   place).  Either one is checked: the semantics of the text must give the
   positions of the selector.  When law 3 was used, the output says that
   the pattern may mean something else on other goals.  Otherwise "no
   ssreflect form" and the reason.

   After a flattening by law 3, the context of the flattened hole is made
   as small as anti-unification allows (the generalization of select_all,
   subterm_select.v: against the earlier same-key competitors in the whole
   part, a smallest hitting set of the disagreement places), and kept only
   if it still denotes the same positions.

   Robustness (sel-robustness, section Robustness below): for a leaf, the
   smallest margin against a LATER competitor with the same key, the
   margin being the number of places of their lgg's disagreement that the
   pattern keeps; 0 means it would silently move to that later subterm if
   the goal changed before it.  Composed by minimum; a pick adds its left
   out later copies at margin 0; a path has no competitor.

   Tactics (the goal is unchanged; "H" optional, a hypothesis):
     elpi sel_denote ["H"] "<selector>".   positions, normal form,
                                           robustness, ssreflect form
     elpi sel_to_ssr ["H"] "<selector>".   the ssreflect pattern, or why none
   For the tests:
     elpi sel_denote_expect ["H"] "<s>" "2.1 3"      ("error" if it fails)
     elpi sel_normal_expect ["H"] "<s>" "<normal form, in the syntax above>"
     elpi sel_to_ssr_expect ["H"] "<s>" "{2}[_ + d]"  ("none" if no form)
     elpi sel_robustness_expect ["H"] "<s>" "1 2.2"   (margin, then the
                                  competitors at it; "none": no competitor)
*)

From elpi Require Import elpi.
From coq_tmp.select Require Export subterm_select.

Elpi Db subterm_algebra.db lp:{{
% [alg-named N S] the name N stands for the selector of text S (sel_define)
pred alg-named o:string, o:string.
}}.

Elpi File subterm_algebra.elpi lp:{{

/* ---------------- Reading a selector ---------------- */

kind atok type.
type at-int int -> atok.
type at-id string -> atok.
type at-angle string -> atok.   % the text inside < >
type at-brack string -> atok.   % an ssreflect pattern [ .. ], brackets kept
type at-sym string -> atok.     % ; # ++ ( ) { } -

pred alg-digit i:string.
alg-digit C :- rex.match "^[0-9]$" C.
pred alg-idchar i:string.
alg-idchar C :- rex.match "^[A-Za-z0-9_']$" C.
pred alg-ident i:string.
alg-ident X :- rex.match "^[A-Za-z_][A-Za-z0-9_']*$" X.

% [alg-span P Cs Ys R] Ys is the longest prefix of Cs whose characters
% satisfy P, R the rest
pred alg-span i:(pred i:string), i:list string, o:list string, o:list string.
alg-span P [C|Cs] [C|Ys] R :- P C, !, alg-span P Cs Ys R.
alg-span _ Cs [] Cs.

pred alg-concat i:list string, o:string.
alg-concat L S :- std.string.concat "" L S.

% [alg-lex Cs Ts] Ts are the tokens of the characters Cs
pred alg-lex i:list string, o:list atok.
alg-lex [] [] :- !.
alg-lex [C|Cs] Ts :- sel-blank C, !, alg-lex Cs Ts.
alg-lex ["<"|Cs] [at-angle S|Ts] :- !,
  alg-angle-body Cs 0 "" [] Body R, alg-concat Body S0, sel-trim S0 S, alg-lex R Ts.
alg-lex ["["|Cs] [at-brack S|Ts] :- !,
  alg-brack-body ["["|Cs] 0 [] Body R, alg-concat Body S, alg-lex R Ts.
alg-lex ["{"|Cs] [at-brack S|Ts] :-   % an ssreflect pattern with its switch
  alg-brack-body ["{"|Cs] 0 [] Occ R0, alg-span sel-blank R0 _ ["["|R1], !,
  alg-brack-body ["["|R1] 0 [] Body R, std.append Occ Body All, alg-concat All S, alg-lex R Ts.
alg-lex ["+", "+"|Cs] [at-sym "++"|Ts] :- !, alg-lex Cs Ts.
alg-lex ["."|Cs] [at-sym ";"|Ts] :- !, alg-lex Cs Ts.
alg-lex [C|Cs] [at-sym C|Ts] :- std.mem! [";", "#", "(", ")", "{", "}", "-"] C, !, alg-lex Cs Ts.
alg-lex [C|Cs] [at-int N|Ts] :- alg-digit C, !,
  alg-span alg-digit [C|Cs] Ds R, alg-concat Ds S, N is string_to_int S, alg-lex R Ts.
alg-lex [C|Cs] [at-id S|Ts] :- alg-idchar C, !,
  alg-span alg-idchar [C|Cs] Ds R, alg-concat Ds S, alg-lex R Ts.

% [alg-angle-body Cs D Prev Acc Body R] Body are the characters up to the
% > that closes < (depth D of the other brackets, Prev the character
% before), R those after it
pred alg-angle-body i:list string, i:int, i:string, i:list string, o:list string, o:list string.
alg-angle-body [">"|Cs] 0 Prev Acc Body Cs :- not (Prev = "-"), not (Prev = "="), !, std.rev Acc Body.
alg-angle-body [C|Cs] D _ Acc Body R :- sel-depth C D D1, alg-angle-body Cs D1 C [C|Acc] Body R.

% [alg-brack-body Cs D Acc Body R] Body are the characters of Cs up to the
% one that brings the depth back to 0, included
pred alg-brack-body i:list string, i:int, i:list string, o:list string, o:list string.
alg-brack-body [C|Cs] D Acc Body R :- sel-depth C D D1,
  (D1 = 0, !, std.rev [C|Acc] Body, R = Cs ; alg-brack-body Cs D1 [C|Acc] Body R).

% [alg-parse S Sel] Sel is the selector of text S
pred alg-parse i:string, o:selector.
alg-parse S0 Sel :-
  rex.replace "⟨" "<" S0 S1, rex.replace "⟩" ">" S1 S2,
  rex.replace "∪" " ++ " S2 S3, rex.replace "ε" " root " S3 S,
  sel-chars S Cs, alg-lex Cs Ts, alg-p-union Ts Sel [].

pred alg-p-union i:list atok, o:selector, o:list atok.
alg-p-union Ts S R :- alg-p-then Ts A R1, alg-p-union-rest A R1 S R.
pred alg-p-union-rest i:selector, i:list atok, o:selector, o:list atok.
alg-p-union-rest A [at-sym "++"|Ts] S R :- !, alg-p-then Ts B R1, alg-p-union-rest (s-union A B) R1 S R.
alg-p-union-rest A R A R.

pred alg-p-then i:list atok, o:selector, o:list atok.
alg-p-then Ts S R :- alg-p-pick Ts A R1, alg-p-then-rest A R1 S R.
pred alg-p-then-rest i:selector, i:list atok, o:selector, o:list atok.
alg-p-then-rest A [at-sym ";"|Ts] S R :- !, alg-p-pick Ts B R1, alg-p-then-rest (s-then A B) R1 S R.
alg-p-then-rest A R A R.

pred alg-p-pick i:list atok, o:selector, o:list atok.
alg-p-pick Ts S R :- alg-p-atom Ts A R1, alg-p-pick-rest A R1 S R.
pred alg-p-pick-rest i:selector, i:list atok, o:selector, o:list atok.
alg-p-pick-rest A [at-sym "#"|Ts] S R :- !, alg-p-k Ts K R1, alg-p-pick-rest (s-pick A K) R1 S R.
alg-p-pick-rest A R A R.

pred alg-p-k i:list atok, o:pick, o:list atok.
alg-p-k [at-sym "{"|Ts] K R :- !, alg-p-kb Ts K [at-sym "}"|R].
alg-p-k Ts K R :- alg-p-kb Ts K R.
pred alg-p-kb i:list atok, o:pick, o:list atok.
alg-p-kb [at-sym "-"|Ts] (pick-out Is) R :- !, alg-ints Ts Is R, Is = [_|_].
alg-p-kb Ts (pick-in Is) R :- alg-ints Ts Is R, Is = [_|_].
pred alg-ints i:list atok, o:list int, o:list atok.
alg-ints [at-int I|Ts] [I|Is] R :- !, alg-ints Ts Is R.
alg-ints R [] R.

pred alg-p-atom i:list atok, o:selector, o:list atok.
alg-p-atom [at-int I|R] (s-step I) R :- !.
alg-p-atom [at-id "root"|R] s-root R :- !.
alg-p-atom [at-id N|R] (s-name N) R :- !.
alg-p-atom [at-angle A|R] S R :- !, alg-angle A S.
alg-p-atom [at-brack B|R] S R :- !, sel-parse B P, sel-of-pat P S.
alg-p-atom [at-sym "("|Ts] S R :- alg-p-union Ts S [at-sym ")"|R].

% [alg-angle A S] S is the selector written <A>
pred alg-angle i:string, o:selector.
alg-angle A S :- sel-chars A Cs, alg-split-bar Cs 0 [] L R, !,
  alg-concat L C0, alg-concat R R0, sel-trim C0 C, alg-hole-rest C R0 S.
alg-angle A (s-match T) :- sel-trim A T.

% [alg-split-bar Cs D Acc L R] Cs are L, a | at depth 0 (not in ||), R
pred alg-split-bar i:list string, i:int, i:list string, o:list string, o:list string.
alg-split-bar ["|"|Cs] 0 Acc L Cs :- not (Cs = ["|"|_]), not (Acc = ["|"|_]), !, std.rev Acc L.
alg-split-bar [C|Cs] D Acc L R :- sel-depth C D D1, alg-split-bar Cs D1 [C|Acc] L R.

pred alg-hole-rest i:string, i:string, o:selector.
alg-hole-rest C R (s-hole-as T X C) :- rex.split ":=" R [X0, T0], !,
  sel-trim X0 X, sel-trim T0 T, alg-ident X.
alg-hole-rest C R (s-hole C X) :- sel-trim R X, alg-ident X.

/* ---------------- Writing a selector ---------------- */

% [alg-text S T] T is the selector S in the concrete syntax (it reads back)
pred alg-text i:selector, o:string.
alg-text s-root "root".
alg-text (s-step I) S :- S is int_to_string I.
alg-text (s-match T) S :- S is "<" ^ T ^ ">".
alg-text (s-hole C X) S :- S is "<" ^ C ^ " | " ^ X ^ ">".
alg-text (s-hole-as T X C) S :- S is "<" ^ C ^ " | " ^ X ^ " := " ^ T ^ ">".
alg-text (s-then A B) S :- alg-text-then A SA, alg-text-then B SB, S is SA ^ " ; " ^ SB.
alg-text (s-pick A K) S :- alg-text-pick A SA, alg-k-text K KS, S is SA ^ " # " ^ KS.
alg-text (s-union A B) S :- alg-text A SA, alg-text B SB, S is SA ^ " ++ " ^ SB.
alg-text (s-name N) N.
pred alg-text-then i:selector, o:string.
alg-text-then (s-union _ _ as A) S :- !, alg-text A SA, S is "(" ^ SA ^ ")".
alg-text-then A S :- alg-text A S.
pred alg-text-pick i:selector, o:string.
alg-text-pick (s-union _ _ as A) S :- !, alg-text A SA, S is "(" ^ SA ^ ")".
alg-text-pick (s-then _ _ as A) S :- !, alg-text A SA, S is "(" ^ SA ^ ")".
alg-text-pick A S :- alg-text A S.
pred alg-k-text i:pick, o:string.
alg-k-text (pick-in [I]) S :- !, S is int_to_string I.
alg-k-text K S :- sel-pick-text K S.

/* ---------------- Names ---------------- */

% [alg-lookup N S] the name N stands for S (sel_define first, then the
% names of subterm_select.v)
pred alg-lookup i:string, o:selector.
alg-lookup N S :- alg-named N Txt, alg-parse Txt S, !.
alg-lookup N S :- sel-named N S, !.

% [alg-expand S S1] S1 is S with its names replaced by what they stand for
pred alg-expand i:selector, o:selector.
alg-expand (s-name N) S :- alg-lookup N S0, !, alg-expand S0 S.
alg-expand (s-then A B) (s-then A1 B1) :- !, alg-expand A A1, alg-expand B B1.
alg-expand (s-pick A K) (s-pick A1 K) :- !, alg-expand A A1.
alg-expand (s-union A B) (s-union A1 B1) :- !, alg-expand A A1, alg-expand B B1.
alg-expand S S.

/* ---------------- Denotation ---------------- */

% [alg-leaf-text S Txt] S is a leaf: the ssreflect pattern of text Txt
pred alg-leaf-text i:selector, o:string.
alg-leaf-text (s-match T) T.
alg-leaf-text (s-hole C X) S :- S is X ^ " in " ^ C.
alg-leaf-text (s-hole-as T X C) S :- S is T ^ " as " ^ X ^ " in " ^ C.

% [alg-leaf-form S F] the form (subterm_select.v) of the leaf S
pred alg-leaf-form i:selector, o:sel-form.
alg-leaf-form (s-match T) (sf-term T).
alg-leaf-form (s-hole C X) (sf-in X C).
alg-leaf-form (s-hole-as T X C) (sf-as-in T X C).

% [alg-denote G H T P S R] R is what S denotes read at the place P of T,
% the part H of the goal G; positions are paths of T
pred alg-denote i:goal, i:string, i:term, i:list int, i:selector, o:sel-res.
alg-denote _ _ _ P s-root (sel-ok [sp-at P]) :- !.
alg-denote _ _ T P (s-step I) R :- !, std.append P [I] PI,
  (path-of T PI, !, R = sel-ok [sp-at PI] ; R = sel-ok []).
alg-denote G H T P S R :- alg-leaf-text S Txt, !, alg-leaf-denote G H T P "" Txt R.
alg-denote G H T P (s-then A B) R :- !, alg-denote G H T P A RA,
  (RA = sel-ok Qs, !, alg-then-each G H T Qs B [] R ; R = RA).
alg-denote G H T P (s-pick A K) R :- !, alg-denote G H T P A RA,
  (RA = sel-ok Qs, !, sel-pick-ranks Qs K 1 Qs1, R = sel-ok Qs1 ; R = RA).
alg-denote G H T P (s-union A B) R :- !, alg-denote G H T P A RA, alg-denote G H T P B RB,
  (RA = sel-ok QA, RB = sel-ok QB, !, sel-merge QA QB Q, R = sel-ok Q ;
   RA = sel-error _, !, R = RA ; R = RB).
alg-denote G H T P (s-name N) R :- alg-lookup N S, !, alg-denote G H T P S R.
alg-denote _ _ _ _ (s-name N) (sel-error M) :- M is "unknown name " ^ N.

% [alg-leaf-denote G H T P Occ Txt R] the oracle on the pattern Txt (with
% the occurrence switch Occ) at the place P of T
pred alg-leaf-denote i:goal, i:string, i:term, i:list int, i:string, i:string, o:sel-res.
alg-leaf-denote G H T [] Occ Txt R :- !, sel-oracle G H Occ Txt R0, sel-norm-res T R0 R.
alg-leaf-denote G _ T P Occ Txt R :- term-at P T _, !,
  sel-box-oracle-occ G T P Occ Txt R0, sel-norm-res T R0 R.
alg-leaf-denote _ _ _ _ _ _
  (sel-error "the place uses a variable bound in the goal: the oracle cannot be run there").

% [alg-then-each G H T Qs B Acc R] B read inside each position of Qs
pred alg-then-each i:goal, i:string, i:term, i:list sel-pos, i:selector,
                   i:list sel-pos, o:sel-res.
alg-then-each _ _ _ [] _ Acc (sel-ok Acc).
alg-then-each G H T [sp-at Q|Qs] B Acc R :- alg-denote G H T Q B RB,
  (RB = sel-ok QB, !, sel-merge Acc QB Acc1, alg-then-each G H T Qs B Acc1 R ; R = RB).
alg-then-each _ _ _ [sp-prefix _ _|_] _ _
  (sel-error "a prefix of an application has no subterms to read a selector in").

% [alg-places G H T Ps S Ps1] Ps1 are the positions S gives read at the
% places Ps (none if it fails somewhere)
pred alg-places i:goal, i:string, i:term, i:list (list int), i:selector, o:list (list int).
alg-places G H T Ps S Ps1 :-
  std.map Ps (p\ r\ alg-denote G H T p S r) Rs,
  std.forall Rs (r\ sigma Qs\ r = sel-ok Qs, std.forall Qs (q\ sigma Q\ q = sp-at Q)), !,
  std.map Rs (r\ l\ sigma Qs\ r = sel-ok Qs, std.map Qs sel-pos-path l) Ls,
  std.flatten Ls Ps0, alg-uniq Ps0 Ps1.
alg-places _ _ _ _ _ [].

pred alg-uniq i:list A, o:list A.
alg-uniq [] [].
alg-uniq [X|Xs] Ys :- std.mem! Xs X, !, alg-uniq Xs Ys.
alg-uniq [X|Xs] [X|Ys] :- alg-uniq Xs Ys.

pred alg-same-res i:sel-res, i:sel-res.
alg-same-res (sel-ok A) (sel-ok A).
alg-same-res (sel-error _) (sel-error _).

pred alg-res-string i:sel-res, o:string.
alg-res-string (sel-ok Qs) S :- !, sel-positions-string Qs S.
alg-res-string (sel-error _) "error".

/* ---------------- Picks (law 5) ---------------- */

% [alg-isort L S] S is L sorted, without repetitions
pred alg-isort i:list int, o:list int.
alg-isort L S :- std.fold L [] alg-ins S.
pred alg-ins i:int, i:list int, o:list int.
alg-ins X [] [X].
alg-ins X [X|L] [X|L] :- !.
alg-ins X [Y|L] [X, Y|L] :- X < Y, !.
alg-ins X [Y|L] [Y|L1] :- alg-ins X L L1.

% [alg-nth-rank K J R] R is the J-th rank (from 1) that K keeps
pred alg-nth-rank i:pick, i:int, o:int.
alg-nth-rank (pick-in Is) J R :- alg-isort Is S, J >= 1, J1 is J - 1,
  std.length S N, J1 < N, std.nth J1 S R.
alg-nth-rank (pick-out Os) J R :- J >= 1, alg-isort Os S, alg-nth-out S 1 J R.
pred alg-nth-out i:list int, i:int, i:int, o:int.
alg-nth-out S I J R :- std.mem! S I, !, I1 is I + 1, alg-nth-out S I1 J R.
alg-nth-out _ I 1 I :- !.
alg-nth-out S I J R :- I1 is I + 1, J1 is J - 1, alg-nth-out S I1 J1 R.

% [alg-pick-compose K K' K2] (s # K) # K' = s # K2
pred alg-pick-compose i:pick, i:pick, o:pick.
alg-pick-compose K (pick-in Js) (pick-in Rs) :- !,
  std.map-filter Js (j\ r\ alg-nth-rank K j r) Rs0, alg-isort Rs0 Rs.
alg-pick-compose (pick-in Is) (pick-out Ms) (pick-in Rs) :- !,
  alg-isort Is S, alg-drop-ranks S 1 Ms Rs.
alg-pick-compose (pick-out Os) (pick-out Ms) (pick-out Rs) :-
  std.map-filter Ms (m\ r\ alg-nth-rank (pick-out Os) m r) Extra,
  std.append Os Extra A, alg-isort A Rs.
pred alg-drop-ranks i:list int, i:int, i:list int, o:list int.
alg-drop-ranks [] _ _ [].
alg-drop-ranks [X|Xs] I Ms Rs :- I1 is I + 1,
  (std.mem! Ms I, !, Rs = Rs1 ; Rs = [X|Rs1]), alg-drop-ranks Xs I1 Ms Rs1.

/* ---------------- The normalizer ---------------- */

% [alg-chain S L] law 1: L is the then-chain S, flat, without roots
pred alg-chain i:selector, o:list selector.
alg-chain (s-then A B) L :- !, alg-chain A LA, alg-chain B LB, std.append LA LB L.
alg-chain s-root [] :- !.
alg-chain S [S].
pred alg-unchain i:list selector, o:selector.
alg-unchain [] s-root.
alg-unchain [S] S :- !.
alg-unchain [S|Ss] (s-then S R) :- alg-unchain Ss R.

% [sel-normalize G H S N Notes] N is the normal form of the selector S on
% the part H of the goal G; Notes say which laws were used (law 3 only
% where its side condition holds on this goal)
pred sel-normalize i:goal, i:string, i:selector, o:selector, o:list string.
sel-normalize G H S N Notes :- sel-part G H T, alg-expand S S1,
  alg-norm G H T [[]] S1 N [] Notes0, std.rev Notes0 Notes.

% [alg-norm G H T Ps S N No0 No] N is S normalized, S being read at the
% places Ps of T; No is No0 with the notes of the laws used
pred alg-norm i:goal, i:string, i:term, i:list (list int), i:selector, o:selector,
              i:list string, o:list string.
alg-norm G H T Ps (s-then _ _ as S) N No0 No :- !, alg-chain S L,
  alg-norm-elems G H T Ps L E No0 No1, alg-merge G H T E L1 No1 No, alg-unchain L1 N.
alg-norm _ _ _ _ (s-hole-as "_" X C) (s-hole C X) No [M|No] :- !,
  M is "law 4: <" ^ C ^ " | " ^ X ^ " := _> is <" ^ C ^ " | " ^ X ^ ">".
alg-norm G H T Ps (s-pick A K) N No0 No :- !, alg-norm G H T Ps A A1 No0 No1,
  (A1 = s-pick A0 K0, !, alg-pick-compose K0 K K1, alg-k-text K0 T0, alg-k-text K TK, alg-k-text K1 T1,
   M is "law 5: # " ^ T0 ^ " # " ^ TK ^ " is # " ^ T1,
   alg-pick-simplify G H T Ps A0 K1 N [M|No1] No ;
   alg-pick-simplify G H T Ps A1 K N No1 No).
alg-norm G H T Ps (s-union A B) (s-union A1 B1) No0 No :- !,
  alg-norm G H T Ps A A1 No0 No1, alg-norm G H T Ps B B1 No1 No.
alg-norm _ _ _ _ S S No No.

% [alg-pick-simplify G H T Ps A K N No0 No] N is A # K, or A when K keeps
% all the positions of A at the places Ps (law 5)
pred alg-pick-simplify i:goal, i:string, i:term, i:list (list int), i:selector, i:pick,
                       o:selector, i:list string, o:list string.
alg-pick-simplify _ _ _ _ A (pick-out []) A No ["law 5: # {-} keeps all"|No] :- !.
alg-pick-simplify G H T Ps A K A No [M|No] :- Ps = [_|_],
  std.forall Ps (p\ sigma Qs\ alg-denote G H T p A (sel-ok Qs), sel-pick-ranks Qs K 1 Qs),
  !, alg-k-text K KS, M is "law 5: # " ^ KS ^ " keeps all the positions here".
alg-pick-simplify _ _ _ _ A K (s-pick A K) No No.

% [alg-norm-elems G H T Ps L E No0 No] the elements of the chain L
% normalized, each with the places where it is read
pred alg-norm-elems i:goal, i:string, i:term, i:list (list int), i:list selector,
                    o:list (pair selector (list (list int))), i:list string, o:list string.
alg-norm-elems _ _ _ _ [] [] No No.
alg-norm-elems G H T Ps [S|Ss] [pr N Ps|Rs] No0 No :-
  alg-norm G H T Ps S N No0 No1, alg-places G H T Ps N Ps1,
  alg-norm-elems G H T Ps1 Ss Rs No1 No.

% [alg-merge G H T E L No0 No] law 3 on the neighbours of the chain E
pred alg-merge i:goal, i:string, i:term, i:list (pair selector (list (list int))),
               o:list selector, i:list string, o:list string.
alg-merge _ _ _ [] [] No No.
alg-merge G H T [pr A PA, pr B _|R] L No0 No :- alg-law3 G H T PA A B M Note, !,
  alg-merge G H T [pr M PA|R] L [Note|No0] No.
alg-merge G H T [pr A _|R] L No0 No :- alg-chain A LA, alg-merge G H T R LB No0 No,
  std.append LA LB L.

% [alg-outer S O] O is the outer term of the hole S, its holes as _
pred alg-outer i:selector, o:string.
alg-outer (s-hole C Y) O :- sel-outer (sf-in Y C) O.
alg-outer (s-hole-as T Y C) O :- sel-outer (sf-as-in T Y C) O.

% [alg-law3 G H T Ps A B M Note] law 3: A ; B is M at the places Ps
pred alg-law3 i:goal, i:string, i:term, i:list (list int), i:selector, i:selector,
              o:selector, o:string.
alg-law3 G H T Ps (s-hole C1 X) B M Note :- Ps = [_|_],
  (B = s-hole C2 Y, ! ; B = s-hole-as _ Y C2),
  (Y = X, ! ; not (rex.match {calc (".*\\b" ^ Y ^ "\\b.*")} C1)),
  sel-replace-var X {calc ("(" ^ C2 ^ ")")} C1 C12,
  (B = s-hole _ _, !, M = s-hole C12 Y ; B = s-hole-as T2 _ _, M = s-hole-as T2 Y C12),
  alg-outer B Out,
  std.forall Ps (p\ alg-law3-at G H T p C1 X Out),
  std.forall Ps (p\ sigma R\ alg-denote G H T p (s-then (s-hole C1 X) B) R, R = sel-ok _,
                    alg-denote G H T p M R),
  alg-text (s-then (s-hole C1 X) B) TL, alg-text M TM,
  Note is "law 3: " ^ TL ^ " is " ^ TM ^ " on this goal (the X part of the first " ^ C1 ^
          " is an instance of " ^ Out ^ ")".

% [alg-law3-at G H T P C1 X Out] at the place P, the X part of the first
% instance of C1 is an instance of Out
pred alg-law3-at i:goal, i:string, i:term, i:list int, i:string, i:string, i:string.
alg-law3-at G H T P C1 X Out :-
  alg-denote G H T P (s-hole C1 X) (sel-ok [sp-at Q|_]),
  sel-box-oracle G T Q Out (sel-ok Qs), std.mem! Qs (sp-at Q).

/* ---------------- Translation to ssreflect ---------------- */

kind ssr-ans type.
type ssr-form string -> list string -> ssr-ans.   % the pattern, warnings
type ssr-none string -> ssr-ans.                  % the reason

% [alg-ssr-shape N Occ Txt] the normal form N is the ssreflect pattern Txt
% with the occurrence switch Occ
pred alg-ssr-shape i:selector, o:string, o:string.
alg-ssr-shape (s-pick A K) Occ Txt :- !, alg-ssr-plain A Txt, sel-pick-text K Occ.
alg-ssr-shape A "" Txt :- alg-ssr-plain A Txt.
pred alg-ssr-plain i:selector, o:string.
alg-ssr-plain (s-then (s-hole C X) (s-match T)) S :- !, S is T ^ " in " ^ X ^ " in " ^ C.
alg-ssr-plain S Txt :- alg-leaf-text S Txt.

pred alg-pat-text i:string, i:string, o:string.
alg-pat-text Occ Txt S :- S is Occ ^ "[" ^ Txt ^ "]".

% [alg-oracle-res G H T Occ Txt R] what the ssreflect pattern selects
pred alg-oracle-res i:goal, i:string, i:term, i:string, i:string, o:sel-res.
alg-oracle-res G H T Occ Txt R :- sel-oracle G H Occ Txt R0, sel-norm-res T R0 R.

% [alg-to-ssr G H S A] A is the ssreflect form of S on the part H of G
pred alg-to-ssr i:goal, i:string, i:selector, o:ssr-ans.
alg-to-ssr G H S A :- sel-part G H T, alg-expand S S1, alg-denote G H T [] S1 D,
  sel-normalize G H S1 N No,
  (alg-ssr-shape N Occ Txt, alg-oracle-res G H T Occ Txt D1, alg-same-res D D1, !,
   std.filter No (n\ starts-with "law 3" n) L3,
   (L3 = [], !, W = [], Txt1 = Txt ;
    W0 = "flattened by law 3, whose side condition holds on this goal: on other goals the pattern may mean something else",
    (Occ = "", alg-minimize G H T N D Txt1, alg-smaller N Txt1 Txt, !,
     W = [W0, {calc ("context made smaller by anti-unification, from [" ^ Txt ^ "]")}] ;
     Txt1 = Txt, W = [W0])),
   alg-pat-text Occ Txt1 PT, A = ssr-form PT W ;
   alg-ssr-occ G H T D A).


% [alg-smaller N Txt1 Txt] the pattern Txt1 keeps fewer symbols than Txt, the
% pattern of the hole N (its variable read as X)
pred alg-smaller i:selector, i:string, i:string.
alg-smaller N Txt1 Txt :- (N = s-hole _ Y ; N = s-hole-as _ Y _), !,
  sel-replace-var Y "X" Txt TxtX, sg-symbols TxtX N0, sg-symbols Txt1 N1, N1 < N0.

% [alg-minimize G H T N D Txt] Txt is the hole N (flattened by law 3),
% denoting D, with its context generalized by anti-unification against the
% earlier competitors with its key in the whole part T (the predicates of
% select_all, subterm_select.v: sg-competitors, sg-dsets, sg-hitting,
% sg-print-ctx, sg-build); checked: Txt denotes D
pred alg-minimize i:goal, i:string, i:term, i:selector, i:sel-res, o:string.
alg-minimize G H T N (sel-ok ([sp-at P|_] as Qs)) Txt :-
  (N = s-hole _ _ ; N = s-hole-as _ _ _), alg-outer N Out,
  alg-oracle-res G H T "" Out (sel-ok [sp-at A|_]),
  term-at A T TA, sg-drop A P R, sg-plain-chain TA R, sg-key TA K, term-at P T Tt,
  sg-competitors T A K Cs, coq.typecheck Tt Ty ok,
  (N = s-hole _ _, !,
   sg-dsets TA (sg-wild R) Cs Dss, sg-hitting TA (sg-wild R) Dss Kp _,
   sg-print-ctx Ty TA Kp R C0, Txt is "X in " ^ C0 ;
   sg-dsets TA (sg-full R) Cs Dss, sg-hitting TA (sg-full R) Dss Kp _,
   std.filter Kp (k\ not (sel-prefix-of R k)) Kc,
   std.map-filter Kp (k\ r\ sg-drop R k r) Kt,
   sg-print-ctx Ty TA Kc R C0,
   sg-build Tt [] Kt sg-none {{ True }} PatT, sg-print PatT St,
   Txt is St ^ " as X in " ^ C0),
  alg-oracle-res G H T "" Txt D1, alg-same-res (sel-ok Qs) D1, !.

% [alg-ssr-occ G H T D A] the positions D written as occurrences of one term
pred alg-ssr-occ i:goal, i:string, i:term, i:sel-res, o:ssr-ans.
alg-ssr-occ _ _ _ (sel-error M) (ssr-none R) :- !,
  R is "the selector fails on this goal (" ^ M ^ ")".
alg-ssr-occ _ _ _ (sel-ok []) (ssr-none "the selector selects nothing on this goal") :- !.
alg-ssr-occ _ _ _ (sel-ok Qs) (ssr-none "a position is a prefix of an application") :-
  std.exists Qs (q\ sigma P K\ q = sp-prefix P K), !.
alg-ssr-occ _ _ T (sel-ok [sp-at P1|_]) A :- not (term-at P1 T _), !,
  A = ssr-none "the position uses a variable bound in the goal: no pattern names it alone".
alg-ssr-occ _ _ T (sel-ok ([sp-at P1|_] as Qs)) A :- term-at P1 T Sub,
  not (std.forall Qs (q\ sigma P S\ q = sp-at P, term-at P T S, same_term S Sub)), !,
  A = ssr-none "the positions are not occurrences of one term: an ssreflect pattern selects the occurrences of one instance".
alg-ssr-occ G H T (sel-ok ([sp-at P1|_] as Qs)) A :- text-at P1 T Txt,
  alg-oracle-res G H T "" Txt (sel-ok Os), std.forall Qs (q\ std.mem! Os q), !,
  alg-ranks Os Qs 1 Ks, std.length Os NO, std.length Ks NK,
  (NK = NO, !, Occ = "" ; sel-pick-text (pick-in Ks) Occ),
  alg-oracle-res G H T Occ Txt D1,
  (alg-same-res (sel-ok Qs) D1, !, alg-pat-text Occ Txt PT,
   A = ssr-form PT ["written as occurrences of the term at the position on this goal (A2/E1): it no longer describes the place"] ;
   alg-pat-text Occ Txt PT, alg-res-string D1 DS,
   A = ssr-none {calc ("the occurrences " ^ PT ^ " select " ^ DS ^ " instead")}).
alg-ssr-occ _ _ _ _ (ssr-none "the term at the position, printed, does not select it back").

pred alg-ranks i:list sel-pos, i:list sel-pos, i:int, o:list int.
alg-ranks [] _ _ [].
alg-ranks [O|Os] Qs I Ks :- I1 is I + 1,
  (std.mem! Qs O, !, Ks = [I|Ks1] ; Ks = Ks1), alg-ranks Os Qs I1 Ks1.

/* ---------------- Robustness ---------------- */

/* Our criterion, inspired by Gonthier and Tassi's fail-early principle
   (ITP 2012, section 1, Ex. 2) and by the robustness of web locators
   (ROBULA+), not a notion taken from the literature.  A leaf is matched
   at its instance I (the first subterm, in pre-order, where its outer
   term matches, inside the place where it is read).  Its competitors are
   the LATER subterms with the same key (after I in pre-order, closed, not
   copies of I).  Against a competitor c, the lgg of I and c has holes at
   the disagreement places of I and c (sg-diff of subterm_select.v); the
   margin is the number of these places that the pattern keeps.  A place d
   is kept when the pattern no longer matches I with its subterm at d
   replaced by the one of c (the semantics, on that
   term).  Margin 0: the pattern matches c already, it would silently move
   to c if the goal changed before it.  The robustness of the leaf is the
   smallest margin, with the competitors at it.  Composition: the minimum
   over the parts (s ; s': s and s' at each place of s; unions); s # K adds
   the positions of s that K leaves out after the first one it keeps, at
   margin 0 (copies: a rank says nothing); a path has no competitor. */

kind sel-rob type.
type rob-none sel-rob.                                % no later competitor
type rob-margin int -> list (list int) -> sel-rob.    % smallest margin, at which competitors

pred alg-rob-min i:sel-rob, i:sel-rob, o:sel-rob.
alg-rob-min rob-none R R :- !.
alg-rob-min R rob-none R :- !.
alg-rob-min (rob-margin M A) (rob-margin M B) (rob-margin M C) :- !, std.append A B C0, alg-uniq C0 C.
alg-rob-min (rob-margin M A) (rob-margin N _) (rob-margin M A) :- M < N, !.
alg-rob-min _ R R.

pred alg-rob-mins i:list sel-rob, o:sel-rob.
alg-rob-mins Rs R :- std.fold Rs rob-none (r\ acc\ o\ alg-rob-min acc r o) R.

% [sel-robustness G H T P S R] R is the robustness of S read at the place
% P of T, the part H of G
pred sel-robustness i:goal, i:string, i:term, i:list int, i:selector, o:sel-rob.
sel-robustness _ _ _ _ s-root rob-none :- !.
sel-robustness _ _ _ _ (s-step _) rob-none :- !.
sel-robustness G H T P (s-name N) R :- alg-lookup N S, !, sel-robustness G H T P S R.
sel-robustness _ _ _ _ (s-name _) rob-none :- !.
sel-robustness G H T P (s-then A B) R :- !, sel-robustness G H T P A RA,
  (alg-denote G H T P A (sel-ok Qs), ! ; Qs = []),
  std.map-filter Qs (q\ r\ sigma Q\ q = sp-at Q, sel-robustness G H T Q B r) RBs,
  alg-rob-mins [RA|RBs] R.
sel-robustness G H T P (s-pick A K) R :- !, sel-robustness G H T P A RA,
  (alg-denote G H T P A (sel-ok Qs), ! ; Qs = []),
  sel-pick-ranks Qs K 1 Picked,
  (Picked = [F|_], !, sel-pos-path F FP,
   std.map-filter Qs (q\ p\ not (std.mem! Picked q), sel-pos-path q p, sel-before FP p) Un ;
   Un = []),
  (Un = [], !, R = RA ; alg-rob-min RA (rob-margin 0 Un) R).
sel-robustness G H T P (s-union A B) R :- !, sel-robustness G H T P A RA,
  sel-robustness G H T P B RB, alg-rob-min RA RB R.
sel-robustness G H T P S R :- alg-leaf-form S F, sel-outer F Out,
  alg-leaf-denote G H T P "" Out (sel-ok [sp-at I|_]), term-at I T TI, sg-key TI K, !,
  sel-closed [] T [] [] Ps0, std.rev Ps0 Ps,
  std.filter Ps (q\ sel-prefix-of P q, sel-before I q) Cands,
  std.map-filter Cands (q\ c\ sigma Tq\ term-at q T Tq, sg-key Tq K, not (same_term Tq TI),
                         c = pr q Tq) Comps,
  std.map Comps (alg-margin G TI Out) Rs, alg-rob-mins Rs R.
sel-robustness _ _ _ _ _ rob-none.

% [alg-margin G TI Out Comp R] R is the margin of the pattern of outer
% term Out, matched at TI, against the competitor Comp
pred alg-margin i:goal, i:term, i:string, i:pair (list int) term, o:sel-rob.
alg-margin G TI Out (pr Q C) (rob-margin M [Q]) :-
  sg-diff TI C [] [] Ds, std.filter Ds (alg-kept G TI C Out) Kept, std.length Kept M.

% [alg-kept G TI C Out D] the pattern of outer term Out keeps the place D:
% it does not match TI with its subterm at D replaced by the one of C
pred alg-kept i:goal, i:term, i:term, i:string, i:list int.
alg-kept G TI C Out D :- term-at D C CD, replace-at D [] (_\ _\ r\ r = CD) TI TID, !,
  not (sel-box-oracle G TID [] Out (sel-ok Qs), std.mem! Qs (sp-at [])).
alg-kept _ _ _ _ _.

% [alg-rob-text R S] S describes the robustness R
pred alg-rob-text i:sel-rob, o:string.
alg-rob-text rob-none "robustness: no later competitor with the same key".
alg-rob-text (rob-margin M Ls) S :- std.map Ls string-of-path Ps, std.string.concat " " Ps PS,
  std.length Ls N,
  S is "robustness " ^ {std.any->string M} ^ " (" ^ {std.any->string N} ^
       " later competitor(s) at that margin: " ^ PS ^ ")".

/* ---------------- The tactics ---------------- */

% [alg-read S Sel] Sel is the selector of text S (or the tactic fails)
pred alg-read i:string, o:selector.
alg-read S Sel :- alg-parse S Sel, !.
alg-read S _ :- coq.ltac.fail 0 {msg "cannot read the selector"} S.

pred alg-ssr-line i:ssr-ans, o:string.
alg-ssr-line (ssr-form P W) S :-
  std.map W (w\ s\ s is "\n  warning: " ^ w) Ws, std.string.concat "" Ws WS,
  S is "ssreflect: " ^ P ^ WS.
alg-ssr-line (ssr-none R) S :- S is "no ssreflect form: " ^ R.

pred alg-ssr-short i:ssr-ans, o:string.
alg-ssr-short (ssr-form P _) P.
alg-ssr-short (ssr-none _) "none".

% [alg-report G H S] prints what the selector of text S denotes in the
% part H of G, its normal form, its robustness and its ssreflect form
pred alg-report i:goal, i:string, i:string.
alg-report G H S :- alg-read S Sel, sel-part G H T, alg-text Sel ST,
  alg-denote G H T [] Sel R,
  sel-normalize G H Sel N No, alg-text N NT,
  std.map No (n\ s\ s is "  " ^ n) NoL,
  (R = sel-error M, !, RL = [{calc ("  fails: " ^ M)}] ;
   R = sel-ok Qs, std.map Qs (sel-pos-line T) PL, std.length Qs NQ, sel-count-line NQ CL,
   std.append PL [CL] RL),
  sel-robustness G H T [] Sel Rob, alg-rob-text Rob FragL,
  alg-to-ssr G H Sel A, alg-ssr-line A AL,
  std.flatten [[{calc ("selector " ^ ST ^ ":")}], RL, [{calc ("normal form: " ^ NT)}], NoL,
               [FragL, AL]] All,
  std.string.concat "\n" All Out, coq.say Out.

}}.

(* [Elpi sel_define "N" "<selector>"]: N names the selector *)
Elpi Command sel_define.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate Db subterm_algebra.db.
Elpi Accumulate File subterm_algebra.elpi.
Elpi Accumulate lp:{{
main [str N, str S] :- alg-ident N, alg-parse S _, !,
  coq.elpi.accumulate _ "subterm_algebra.db" (clause _ _ (alg-named N S)).
main _ :- coq.error "sel_define: give a name and a selector that reads".
}}.

Elpi Tactic sel_denote.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate Db subterm_algebra.db.
Elpi Accumulate File subterm_algebra.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "sel_denote" => (sel-args 0 Args H S [], alg-report G H S).
}}.

Elpi Tactic sel_to_ssr.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate Db subterm_algebra.db.
Elpi Accumulate File subterm_algebra.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "sel_to_ssr" => (sel-args 0 Args H S [], alg-read S Sel,
  alg-to-ssr G H Sel A, alg-ssr-line A L, alg-text Sel ST,
  coq.say "selector" ST ":\n" L).
}}.

Elpi Tactic sel_denote_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate Db subterm_algebra.db.
Elpi Accumulate File subterm_algebra.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "sel_denote_expect" => (sel-args 1 Args H S [Exp0], sel-norm-expect Exp0 Exp,
  alg-read S Sel, sel-part G H T, alg-denote G H T [] Sel R, alg-res-string R Got,
  (Got = Exp, ! ; coq.ltac.fail 0 {msg S} ": got" Got "expected" Exp)).
}}.

Elpi Tactic sel_normal_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate Db subterm_algebra.db.
Elpi Accumulate File subterm_algebra.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "sel_normal_expect" => (sel-args 1 Args H S [Exp],
  alg-read S Sel, sel-normalize G H Sel N No, alg-text N Got,
  % the normal form denotes what the selector denotes
  sel-part G H T, alg-denote G H T [] Sel R, alg-denote G H T [] N RN,
  (alg-same-res R RN, ! ; coq.ltac.fail 0 {msg S} ": the normal form" Got "denotes otherwise"),
  (Got = Exp, ! ; coq.ltac.fail 0 {msg S} ": got" Got "expected" Exp "notes" No)).
}}.

Elpi Tactic sel_to_ssr_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate Db subterm_algebra.db.
Elpi Accumulate File subterm_algebra.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "sel_to_ssr_expect" => (sel-args 1 Args H S [Exp],
  alg-read S Sel, alg-to-ssr G H Sel A, alg-ssr-short A Got, alg-ssr-line A L,
  coq.say S "->" L,
  % the round trip: the pattern, read as a selector, denotes what S denotes
  (A = ssr-form P _, !, sel-part G H T, alg-denote G H T [] Sel R,
   alg-read P SelP, alg-denote G H T [] SelP RP,
   (alg-same-res R RP, ! ; coq.ltac.fail 0 {msg S} ": the round trip fails on" P) ; true),
  (Got = Exp, ! ; coq.ltac.fail 0 {msg S} ": got" Got "expected" Exp)).
}}.

Elpi Tactic sel_robustness_expect.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate Db subterm_algebra.db.
Elpi Accumulate File subterm_algebra.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ Args as G) [seal G] :-
  tool-name "sel_robustness_expect" => (sel-args 1 Args H S [Exp0], sel-norm-expect Exp0 Exp,
  alg-read S Sel, sel-part G H T, sel-robustness G H T [] Sel R, alg-rob-text R RT,
  coq.say S ":" RT,
  (R = rob-none, !, Got = "none" ;
   R = rob-margin M Ls, std.map Ls string-of-path Ps,
   std.string.concat " " [{std.any->string M}|Ps] Got),
  (Got = Exp, ! ; coq.ltac.fail 0 {msg S} ": got" Got "expected" Exp)).
}}.
