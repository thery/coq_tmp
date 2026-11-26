(* Support of the differential tests (run.sh): the Elpi semantics of the
   patterns (subterm_select.v) against ssreflect's set.

   Stage 1: [elpi diff_gen "Id"] (every pattern that select_all and
   point_to_pattern produce for every path of the conclusion and of each
   hypothesis that is a proposition) and [elpi diff_cases "Id" ["H"]
   "pat" ...] (given patterns) print one line per case,
     CASE <tab> Id <tab> H <tab> set-text <tab> Elpi result
   the Elpi result being the positions (blank separated, "" for none),
   "error" or "outside" (the supported fragment).  run.sh writes stage 2,
   where each case is
     let G := <the part> in
     first [ assert_succeeds (set pattern_select_z := <set-text> [in H];
                              elpi z_report "Id" "<n>" ltac_term:(G) ["H"])
           | idtac "SSR" ... "error" ]
   and z_report prints the positions of pattern_select_z in the goal that
   set gives (paths of the original part G, as subterm_select.v writes
   them).  run.sh compares the two. *)

From Stdlib Require Import String.
From elpi Require Import elpi.
From coq_tmp.select Require Export subterm_select.
From coq_tmp Require Import pbp_select point_actions point_actions_more.

Elpi File diff_support.elpi lp:{{
% [diff-z-name N] N is the name of the local definition that set adds
pred diff-z-name o:string.
diff-z-name "pattern_select_z".
% [sel-orig C Ty H O] O is the part, before set, of the goal of context C
% and conclusion Ty: Ty (H = "") or the type of the hypothesis H
pred sel-orig i:goal-ctx, i:term, i:string, o:term.
sel-orig _ Ty "" Ty :- !.
sel-orig C _ H T :- (std.mem C (decl _ N T) ; std.mem C (def _ N _ T)), coq.name->id N H, !.
% [sel-open SG H O R] R are the positions of z in the goal SG (in the type
% of its hypothesis H if H is not ""), O the part before set
pred sel-open i:sealed-goal, i:string, i:term, o:sel-res.
sel-open (nabla F) H O R :- pi x\ sel-open (F x) H O R.
sel-open (seal (goal Ctx _ Ty _ _)) H O R :- diff-z-name ZN,
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

% [diff-res R S] S is the result R as written in the CASE lines
pred diff-res i:sel-res, o:string.
diff-res (sel-ok Qs) S :- !, sel-positions-string Qs S.
diff-res (sel-error M) "outside" :- starts-with "outside" M, !.
diff-res (sel-error _) "error".

% [diff-set-text S T] T is the pattern S as set writes it: {occ}(pattern)
pred diff-set-text i:string, o:string.
diff-set-text S T :- sel-parse S (sel-pat Occ Txt _), T is Occ ^ "(" ^ Txt ^ ")".

% [diff-case G Id H S] prints the case of the pattern S in the part H
pred diff-case i:goal, i:string, i:string, i:string.
diff-case G Id H S :- sel-select G H S _ R, diff-res R RS, diff-set-text S T,
  L is "CASE\t" ^ Id ^ "\t" ^ H ^ "\t" ^ T ^ "\t" ^ RS, coq.say L.

% [diff-patterns G Ctx H T Ss] Ss are the patterns of select_all and of
% point_to_pattern for the paths of the part T (H), without repetitions
pred diff-patterns i:goal, i:goal-ctx, i:string, i:term, o:list string.
diff-patterns G Ctx H T Ss :-
  std.findall (path-of T P_) Sols, std.map Sols (s\ p\ s = path-of _ p) Ps,
  std.map Ps (p\ ss\ sigma Rs L1 L2\
     (sg-select-all G H p Rs, !,
      std.map-filter Rs (r\ s\ sigma K\ r = sg-res _ K s _ _, not (K = a1-path)) L1 ; L1 = []),
     (diff-ptp Ctx G H p S2, !, L2 = [S2] ; L2 = []),
     std.append L1 L2 ss) Sss,
  std.flatten Sss Ss0, sg-undup Ss0 Ss.

pred diff-ptp i:goal-ctx, i:goal, i:string, i:list int, o:string.
diff-ptp Ctx (goal _ _ Ty _ _) H P Pat :-
  (H = "", !, Sels = [sel-goal P] ; Sels = [sel-hyp H P]),
  point-resolve Ctx Ty Sels In _, point-local-pattern In Pat.

% [diff-parts G Ctx Hs] Hs are "" and the hypotheses that are propositions
pred diff-parts i:goal-ctx, o:list string.
diff-parts Ctx [""|Hs] :-
  std.map-filter Ctx (e\ h\ sigma V N T S\ e = decl V N T,
     coq.typecheck T S ok, S = sort prop, coq.name->id N h) Hs.
}}.

Elpi Tactic diff_gen.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate File diff_support.elpi.
Elpi Accumulate lp:{{
solve (goal Ctx _ _ _ [str Id] as G) [seal G] :-
  tool-name "diff_gen" => (
  diff-parts Ctx Hs,
  std.forall Hs (h\ sigma T Ss\ sel-part G h T, diff-patterns G Ctx h T Ss,
    std.forall Ss (s\ diff-case G Id h s))).
}}.

Elpi Tactic diff_cases.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate File diff_support.elpi.
Elpi Accumulate lp:{{
solve (goal _ _ _ _ [str Id, str "in", str H | Args] as G) [seal G] :- !,
  tool-name "diff_cases" => std.forall Args (a\ sigma S\ a = str S, diff-case G Id H S).
solve (goal _ _ _ _ [str Id | Args] as G) [seal G] :-
  tool-name "diff_cases" => std.forall Args (a\ sigma S\ a = str S, diff-case G Id "" S).
}}.

Elpi Tactic z_report.
Elpi Accumulate Db pbp_select.db.
Elpi Accumulate File subterm_pattern.elpi.
Elpi Accumulate File subterm_select.elpi.
Elpi Accumulate File diff_support.elpi.
Elpi Accumulate lp:{{
solve (goal Ctx RE Ty E [str Id, str N, trm O | HA] as G) [seal G] :-
  (HA = [str H], ! ; H = ""),
  sel-open (seal (goal Ctx RE Ty E [])) H O R0, sel-norm-res O R0 R, diff-res R S,
  L is "SSR\t" ^ Id ^ "\t" ^ N ^ "\t" ^ S, coq.say L.
}}.
