(* The random part of the differential tests.

   [Elpi diff_random_goals N Seed] prints a corpus file (corpus_random.v,
   written by gen_random.sh): N random goals t1 = t2 over a few symbols
   (variables a b c : nat, l : list nat, f : nat -> nat -> nat,
   g : nat -> nat, numerals 0 to 3, + and *, pairs with fst and snd, lists
   with :: and ++), each one followed by elpi diff_random "rand.<k>" "<seed>".

   [elpi diff_random "Id" "Seed"] (stage 1, in the goal) prints the CASE
   lines (diff_support.v) of 12 random patterns derived from the subterms
   of the goal: a random closed subterm t generalized at random places
   (holes _), and a random form: t, X in C, t in X in C, t as X in C, C
   from a random ancestor of t (generalized at random places, X at t), with
   a random occurrence switch {k} one time out of four. *)
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support.

Elpi File random.elpi lp:{{

% a linear congruential generator: [rnd S S1 N K] N is a number below K
% from the state S, S1 the next state
pred rnd i:int, o:int, o:int, i:int.
rnd S S1 N K :- S1 is (S * 1103515245 + 12345) mod 2147483648, N is (S1 div 65536) mod K.

% [rnd-nat S S1 D T] T is the text of a random term of type nat of depth
% at most D
pred rnd-nat i:int, o:int, i:int, o:string.
rnd-nat S S1 0 T :- !, rnd S S0 N 7, std.nth N ["a", "b", "c", "0", "1", "2", "3"] T, S1 = S0.
rnd-nat S S2 D T :- rnd S S0 N 10, D1 is D - 1,
  (N < 3, !, rnd-nat S0 S2 0 T ;
   N = 3, !, rnd-nat S0 S1 D1 A, rnd-nat S1 S2 D1 B, T is "(" ^ A ^ " + " ^ B ^ ")" ;
   N = 4, !, rnd-nat S0 S1 D1 A, rnd-nat S1 S2 D1 B, T is "(" ^ A ^ " * " ^ B ^ ")" ;
   N = 5, !, rnd-nat S0 S1 D1 A, rnd-nat S1 S2 D1 B, T is "(f " ^ A ^ " " ^ B ^ ")" ;
   N = 6, !, rnd-nat S0 S2 D1 A, T is "(g " ^ A ^ ")" ;
   N = 7, !, rnd-nat S0 S1 D1 A, rnd-nat S1 S2 D1 B, T is "(fst (" ^ A ^ ", " ^ B ^ "))" ;
   N = 8, !, rnd-nat S0 S1 D1 A, rnd-nat S1 S2 D1 B, T is "(snd (" ^ A ^ ", " ^ B ^ "))" ;
   rnd-list S0 S2 D1 L, T is "(length " ^ L ^ ")").

% [rnd-list S S1 D T] a random term of type list nat
pred rnd-list i:int, o:int, i:int, o:string.
rnd-list S S1 0 "l" :- !, S1 = S.
rnd-list S S2 D T :- rnd S S0 N 3, D1 is D - 1,
  (N = 0, !, S2 = S0, T = "l" ;
   N = 1, !, rnd-nat S0 S1 D1 A, rnd-list S1 S2 D1 L, T is "(" ^ A ^ " :: " ^ L ^ ")" ;
   rnd-list S0 S1 D1 L1, rnd-list S1 S2 D1 L2, T is "(" ^ L1 ^ " ++ " ^ L2 ^ ")").

pred rnd-goals i:int, i:int, i:int.
rnd-goals K N _ :- K > N, !.
rnd-goals K N S :- rnd-nat S S1 4 A, rnd-nat S1 S2 4 B,
  coq.say "Goal forall (a b c : nat) (l : list nat)," A "=" B ".",
  coq.say "intros a b c l.",
  coq.say {calc ("elpi diff_random \"rand." ^ int_to_string K ^ "\" \"" ^ int_to_string S2 ^ "\".")},
  coq.say "Abort.\n",
  K1 is K + 1, rnd-goals K1 N S2.

% [rnd-pick S S1 L X] X is a random element of L
pred rnd-pick i:int, o:int, i:list A, o:A.
rnd-pick S S1 L X :- std.length L N, N > 0, rnd S S1 I N, std.nth I L X.

% [rnd-subset S S1 L L1] L1 is a random part of L (each one with
% probability 1/2)
pred rnd-subset i:int, o:int, i:list A, o:list A.
rnd-subset S S [] [] :- !.
rnd-subset S S2 [X|L] L1 :- rnd S S1 N 2, rnd-subset S1 S2 L L0,
  (N = 0, !, L1 = [X|L0] ; L1 = L0).

% [rnd-kept T S S1 K] K is a random set of positions of T to keep (the
% printed ones; the others become holes)
pred rnd-kept i:term, i:int, o:int, o:list (list int).
rnd-kept T S S1 K :- sel-closed [] T [] [] Ps0, std.filter Ps0 (p\ not (p = []), not (sel-hidden T p)) Ps,
  rnd-subset S S1 Ps K.

% [rnd-pattern T S S1 Pat] a random pattern of the part T
pred rnd-pattern i:term, i:int, o:int, o:string.
rnd-pattern T S S6 Pat :-
  sel-closed [] T [] [] Ps0, std.filter Ps0 (p\ term-at p T Tt, sg-key Tt _) Ps,
  rnd-pick S S1 Ps P, term-at P T Tt,
  rnd-kept Tt S1 S2 Kt, sg-build Tt [] Kt sg-none {{ True }} PatT, sg-print PatT St,
  rnd S2 S3 Form 4,
  sg-ancestors P As, std.filter As (a\ sigma R TA\ sg-drop a P R, term-at a T TA, sg-plain-chain TA R, sg-key TA _) As1,
  (Form = 0, !, Txt = St, S4 = S3 ;
   As1 = [], !, Txt = St, S4 = S3 ;
   rnd-pick S3 S30 As1 A, term-at A T TA, sg-drop A P R, coq.typecheck Tt Ty ok,
   rnd-kept TA S30 S31 Kc0, std.filter Kc0 (k\ not (sg-related k R)) Kc,
   (Form = 1, !, sg-print-ctx Ty TA Kc R C0, Txt is "X in " ^ C0, S4 = S31 ;
    Form = 2, !, sg-ancestors R Ms, std.filter Ms (m\ not (m = [])) Ms1,
    (Ms1 = [], !, sg-print-ctx Ty TA Kc R C0, Txt is St ^ " in X in " ^ C0, S4 = S31 ;
     rnd-pick S31 S4 Ms1 M, term-at M TA TM, coq.typecheck TM TyM ok,
     std.filter Kc (k\ not (sg-related k M)) Kc1,
     sg-print-ctx TyM TA Kc1 M C0, Txt is St ^ " in X in " ^ C0) ;
    sg-print-ctx Ty TA Kc R C0, Txt is St ^ " as X in " ^ C0, S4 = S31)),
  rnd S4 S5 O 4,
  (O = 0, !, rnd S5 S6 Kk 3, K1 is Kk + 1, Pat is "{" ^ int_to_string K1 ^ "}(" ^ Txt ^ ")" ;
   S6 = S5, Pat is "(" ^ Txt ^ ")").

}}.

Elpi Command diff_random_goals.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate File random.elpi.
Elpi Accumulate lp:{{
main [int N, int S] :- rnd-goals 1 N S.
}}.

Elpi Tactic diff_random.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate File diff_support.elpi.
Elpi Accumulate File random.elpi.
Elpi Accumulate lp:{{
pred rnd-patterns i:goal, i:string, i:term, i:int, i:int.
rnd-patterns _ _ _ 0 _ :- !.
rnd-patterns G Id T N S :- (rnd-pattern T S S1 Pat, !, diff-case G Id "" Pat ; rnd S S1 _ 2),
  N1 is N - 1, rnd-patterns G Id T N1 S1.
solve (goal _ _ T _ [str Id, str Seed] as G) [seal G] :-
  S0 is string_to_int Seed, rnd-patterns G Id T 12 S0.
}}.
