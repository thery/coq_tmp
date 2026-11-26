From Stdlib Require Import ssreflect.
From elpi Require Import elpi.
(* the patterns [X in ...] of pbp (their notation) *)
From coq_tmp Require Export subterm_pattern.

Definition conjR {A B : Prop} (X : A) (Y : B) := conj Y X.
Lemma and1imp {A B C : Prop} (H : B -> A -> C) : A /\ B -> C.
Proof. by move=> [H1 H2]; apply: H. Qed.
Lemma and2imp {A B C : Prop} (H : A -> B -> C) : A /\ B -> C.
Proof. by move=> [H1 H2]; apply: H. Qed.
Lemma or1imp {A B C : Prop} (H : A -> C) (H1 : B -> C) : A \/ B -> C.
Proof. by move=> [H2|H2]; [apply/H/H2 | apply/H1/H2]. Qed.
Lemma or2imp {A B C : Prop} (H : B -> C) (H1 : A -> C) : A \/ B -> C.
Proof. by move=> [H2|H2]; [apply/H1/H2 | apply/H/H2]. Qed.
Lemma imp1imp {A B C : Prop} (H : A) (H1 : B -> C) (H2 : A -> B) : C.
Proof. by apply/H1/H2. Qed.
Lemma imp2imp {A B C : Prop} (H1 : B -> C) (H : A)  (H2 : A -> B) : C.
Proof. by apply/H1/H2. Qed.
Lemma negimp {A B : Prop} (H : A) (H1 : ~ A) : B.
Proof. by case: H1. Qed.
Lemma impimp1 {A B C : Prop} (H : B -> A -> C) : A -> B -> C.
Proof. by move=> H1 H2; apply: H. Qed.
Lemma and1impimp {A B C D : Prop} (H : B -> A -> C -> D) : A /\ B -> C -> D.
Proof. by move=> [H1 H2]; apply: H. Qed.
Lemma and2impimp {A B C D : Prop} (H : A -> B -> C -> D) : A /\ B -> C -> D.
Proof. by move=> [H1 H2]; apply: H. Qed.
Lemma impand1imp {A B C D : Prop} (H : C -> A -> B -> D) : A -> B /\ C -> D.
Proof. by move=> H0 [H1 H2]; apply: H. Qed.
Lemma impand2imp {A B C D : Prop} (H : B -> A -> C -> D) : A -> B /\ C -> D.
Proof. by move=> H0 [H1 H2]; apply: H. Qed.
Lemma or1impimp {A B C D : Prop} (H : A -> C -> D) (H1 : B -> C -> D) : 
  A \/ B -> C -> D.
Proof. by move=> [H2 |H2]; [apply: H | apply: H1]. Qed.
Lemma or2impimp {A B C D : Prop} (H : B -> C -> D) (H1 : A -> C -> D) : 
  A \/ B -> C -> D.
Proof. by move=> [H2 |H2]; [apply: H1 | apply: H]. Qed.
Lemma impor1imp {A B C D : Prop} (H : A -> B -> D) (H1 : A -> C -> D) : 
  A -> B \/ C -> D.
Proof. by move=> H0 [H2 |H2]; [apply: H | apply: H1]. Qed.
Lemma impor2imp {A B C D : Prop} (H : A -> C -> D) (H1 : A -> B -> D) : 
  A -> B \/ C -> D.
Proof. by move=> H0 [H2 |H2]; [apply: H1 | apply: H]. Qed.
Lemma imp1impimp {A B C D : Prop} (H : C -> A) (H1 : B -> C -> D) : 
  (A -> B) -> C -> D.
Proof. by move=> H2 H3; apply: H1; first apply/H2/H. Qed.
Lemma imp2impimp {A B C D : Prop} (H : B -> C -> D) (H1 : C -> A):
  (A -> B) -> C -> D.
Proof. by move=> H2 H3; apply: H; first apply/H2/H1. Qed.
Lemma impimp1imp {A B C D : Prop} (H : A -> B) (H1 : C -> A -> D) : 
  A -> (B -> C) -> D.
Proof. by move=> H2 H3; apply: H1; first apply/H3/H. Qed.
Lemma impimp2imp {A B C D : Prop} (H : B -> A -> C -> D) (H1 : A -> B):
  A -> (B -> C) -> D.
Proof. by move=> H2 H3; apply: H => //; [apply: H1 | apply/H3/H1]. Qed.
Lemma negimpimp {A B C : Prop} (H : B -> A) :  ~ A -> B -> C.
Proof. by move=> H1 H2; case: H1; apply: H. Qed. 
Lemma impnegimp {A B C : Prop} (H : A -> B): A -> ~ B -> C.
Proof. by move=> H1 []; apply: H. Qed. 
Lemma impand1 {A B C : Prop} (H : A -> B) (H1: A -> C) : A -> B /\ C.
Proof. by move=> H2; split; [apply: H | apply: H1]. Qed.
Lemma impand2 {A B C : Prop} (H : A -> C) (H1: A -> B) : A -> B /\ C.
Proof. by move=> H2; split; [apply: H1 | apply: H]. Qed.
Lemma impor1 {A B C : Prop} (H : A -> B) : A -> B \/ C.
Proof. by move=> H2; left; apply: H. Qed.
Lemma impor2 {A B C : Prop} (H : A -> C) : A -> B \/ C.
Proof. by move=> H2; right; apply: H. Qed.
(* The quantifier rules: an assumption forall x, P x used at a witness w
   (a new evar), an assumption exists x, P x destructured, an exists of
   the goal proved at a witness w, and their variants under a first
   assumption A.  A witness w comes after a marker n, fun name => name:
   the name of its binder is the name pbp gives to the evar of w *)
Lemma pbp_ex_intro {T : Type} {P : T -> Prop} (n : unit -> unit) (w : T)
  (H : P w) : exists x, P x.
Proof. by exists w. Qed.
Lemma pbp_forallimp {T : Type} {P : T -> Prop} {C : Prop} (n : unit -> unit)
  (w : T) (H : P w -> C) : (forall x, P x) -> C.
Proof. by move=> H1; apply/H/H1. Qed.
Lemma pbp_existsimp {T : Type} {P : T -> Prop} {C : Prop}
  (H : forall x, P x -> C) : (exists x, P x) -> C.
Proof. by move=> [x H1]; apply: H H1. Qed.
Lemma pbp_impforallimp {A : Prop} {T : Type} {P : T -> Prop} {C : Prop}
  (n : unit -> unit) (w : T) (H : A -> P w -> C) : A -> (forall x, P x) -> C.
Proof. by move=> H1 H2; apply/H/H2. Qed.
Lemma pbp_impexistsimp {A : Prop} {T : Type} {P : T -> Prop} {C : Prop}
  (H : forall x, A -> P x -> C) : A -> (exists x, P x) -> C.
Proof. by move=> H1 [x H2]; apply: H H1 H2. Qed.
Lemma pbp_impforall {A : Prop} {T : Type} {P : T -> Prop}
  (H : forall x, A -> P x) : A -> forall x, P x.
Proof. by move=> H1 x; apply: H H1. Qed.
Lemma pbp_impexists {A : Prop} {T : Type} {P : T -> Prop} (n : unit -> unit)
  (w : T) (H : A -> P w) : A -> exists x, P x.
Proof. by move=> H1; exists w; apply: H H1. Qed.



Elpi Db pbp_build.db lp:{{

pred pbp_build i:term, i:term, o:term.

/* ---------------- Binders: forall, exists, named premises ----------------
   The pattern is read positionally: under a binder of the goal, the
   binder of the pattern at the same place stands for the same variable
   (forall n, X = 0 points at n).  The names written in the pattern name
   what pbp introduces: the variable of a forall, the hypothesis of a named
   premise (forall (H : A), _ is A -> _), the variable of a destructured
   exists, and the evars (?n) of the witnesses of an exists and of the
   instances of a forall assumption; a name already used in the context
   is an error.  An unnamed premise is introduced as pbp. */

% [pbp_sel X] X is a variable of the pattern (a selection)
pred pbp_sel o:term.

% [has-sel T] T holds a selection (not in the arguments of a hole of the
% pattern: the holes are applied to the variables above them)
pred has-sel i:term.
has-sel T :- pbp_sel V, sel-in V T, !.

% [sel-in V T] the variable V occurs in T, outside its holes
pred sel-in i:term, i:term.
sel-in _ T :- var T, !, fail.
sel-in V V :- !.
sel-in V (app L) :- std.exists L (sel-in V).
sel-in V (prod _ A F) :- sel-in V A, ! ; pi x\ sel-in V (F x).
sel-in V (fun _ A F) :- sel-in V A, ! ; pi x\ sel-in V (F x).
sel-in V (let _ A B F) :- sel-in V A, ! ; sel-in V B, ! ; pi x\ sel-in V (F x).
sel-in V (match A R L) :- sel-in V A, ! ; sel-in V R, ! ; std.exists L (sel-in V).

% [pbp-dep F] the body F uses its variable
pred pbp-dep i:(term -> term).
pbp-dep F :- pi x\ occurs x (F x).

% [pbp-prop T] T is a proposition
pred pbp-prop i:term.
pbp-prop T :- coq.typecheck T S ok, S = sort prop.

% [pbp-quant T F] forall x : T, F x is a quantifier (not an implication)
pred pbp-quant i:term, i:(term -> term).
pbp-quant _ F :- pbp-dep F, !.
pbp-quant T _ :- not (pbp-prop T).

% [pbp-named NP S] the binder name NP of the pattern is written, S (a
% name that is used in the context reaches pbp renamed by Rocq-Elpi
% _elpi_renamed_S_k: it is S)
pred pbp-named i:name, o:string.
pbp-named NP S :- coq.name->id NP S0, not (S0 = "_"),
  (rex.match "^_elpi_renamed_.*_[0-9]+$" S0, !,
   rex.replace "^_elpi_renamed_" "" S0 S1, rex.replace "_[0-9]+$" "" S1 S ;
   S = S0).

% [pbp-name-free S W] the name S, written in the pattern for the binder W
% (forall, exists, premise), is not used in the context: else the error
pred pbp-name-free i:string, i:string.
pbp-name-free S W :- pbp-used S N T D, !,
  (D = tt, !, What = "local definition" ;
   pbp-prop T, !, What = "hypothesis" ; What = "variable"),
  coq.term->string T TS,
  M is "pbp: the name " ^ S ^ " of the " ^ W ^ " in the pattern is already used by the " ^ What ^ " " ^ S ^ " : " ^ TS ^ "; choose another name in the pattern",
  coq.ltac.fail 0 M.
pbp-name-free _ _.

% [pbp_ctx Ctx] Ctx is the context of the goal
pred pbp_ctx o:goal-ctx.

% [pbp_bound N T] pbp has introduced a variable named N of type T
pred pbp_bound o:name, o:term.

% [pbp-used S N T D] a variable of the goal's context, or one introduced
% by pbp so far, is named S (its name N): its type is T, D says if it is a
% local definition
pred pbp-used i:string, o:name, o:term, o:bool.
pbp-used S N T ff :- pbp_bound N T, coq.name->id N S, !.
pbp-used S N T D :- pbp_ctx Ctx, std.mem Ctx E,
  (E = decl _ N T, D = ff ; E = def _ N T _, D = tt), coq.name->id N S, !.

% [pbp-intro-name NP AP N A F Name] Name is the name of the variable (or
% hypothesis) introduced for the goal forall N : A, F, the pattern being
% forall NP : AP, _: the name written in the pattern (checked free), the
% free name of the pattern standing for the premise (get_name), the name
% of the goal for a forall, pbp for a premise
pred pbp-intro-name i:name, i:term, i:name, i:term, i:(term -> term), o:name.
pbp-intro-name NP _ _ A F NP :- pbp-named NP S, !,
  (pbp-quant A F, !, W = "forall" ; W = "premise"), pbp-name-free S W.
pbp-intro-name _ AP _ _ _ H :- get_name AP H, !.
pbp-intro-name _ _ N A F N1 :- pbp-quant A F, !, pbp-fresh N N1.
pbp-intro-name _ _ _ _ _ `pbp`.

% [pbp-exists-name NP N Name] the name of the variable of a destructured
% exists N (exists NP in the pattern)
pred pbp-exists-name i:name, i:name, o:name.
pbp-exists-name NP _ NP :- pbp-named NP S, !, pbp-name-free S "exists".
pbp-exists-name _ N N1 :- pbp-fresh N N1.

% [pbp-fresh N N1] N1 is N, or N with a number (N0, N1, ...), a name not
% used (pbp-used): the name of a binder of the goal that the pattern does
% not name
pred pbp-fresh i:name, o:name.
pbp-fresh N N1 :- coq.name->id N S, pbp-fresh-id S 0 S S1, coq.id->name S1 N1.
pred pbp-fresh-id i:string, i:int, i:string, o:string.
pbp-fresh-id _ _ S S :- not (pbp-used S _ _ _), !.
pbp-fresh-id B I _ S :- S1 is B ^ int_to_string I, I1 is I + 1, pbp-fresh-id B I1 S1 S.

% [pbp-evar NP N T WN W] W is a new evar of type T, to be named after the
% binder NP of the pattern (N of the goal if NP is not written): WN is
% the marker of its name, fun (pbp_evar_name : unit) => pbp_evar_name,
% written just before the witness in the lemmas that take one
% (pbp-name-evars names the evar once the proof is elaborated; the prefix
% keeps Rocq-Elpi from renaming the binder as a name of the context).
% Below the binder, the pattern goes on with a new constant c in place of
% the witness: its holes, applied to the variables bound above them, would
% not be patterns applied to the evar.
pred pbp-evar i:name, i:name, i:term, o:term, o:term.
pbp-evar NP N T (fun Nm {{ unit }} (x\ x)) W :-
  (pbp-named NP S, ! ; coq.name->id N S, not (S = "_"), ! ; S = "x"),
  coq.id->name {calc ("pbp_evar_" ^ S)} Nm,
  coq.typecheck W T ok.

% [pbp-cast Ty R C] C is R written (R : Ty): the goals it leaves have the
% types the walk computed (beta reduced), not the redexes P w of the lemmas
pred pbp-cast i:term, i:term, o:term.
pbp-cast Ty R (let `_` Ty R (x\ x)).

/* One selection.  The invertible rules first (a forall of the goal
   introduced, an exists assumption destructured), so that the evars
   created after them may use their variables */

% a forall (or a premise) of the goal whose type holds no selection: its
% variable (hypothesis) is introduced
pbp_build (prod N A F) (prod NP AP FP) (fun Name A R1) :- not (has-sel AP), !,
  pbp-intro-name NP AP N A F Name,
  pi x\ decl x Name A => pbp_bound Name A => pbp_build (F x) (FP x) (R1 x).
% an assumption exists x, P x: it is destructured
pbp_build (prod H (app [{{ @ex }}, T, fun N T1 P]) (_\ S))
          (prod _ (app [{{ @ex }}, _, fun NP _ P1]) (_\ SP))
    (app [{{ @pbp_existsimp }}, T, fun N T1 P, S, fun Name T RC]) :- !,
  pbp-exists-name NP N Name,
  pi x\ decl x Name T => pbp_bound Name T => sigma G R1\ G = prod H (P x) (_\ S),
    pbp_build G (prod `_` (P1 x) (_\ SP)) R1, pbp-cast G R1 (RC x).
% an assumption forall x, P x: it is used at a new evar
pbp_build (prod H (prod N T P) (_\ S)) (prod _ (prod NP _ P1) (_\ SP))
    (app [{{ @pbp_forallimp }}, T, fun N T P, S, WN, W, RC]) :-
  pbp-quant T P, !,
  pbp-evar NP N T WN W, G = prod H (P W) (_\ S),
  (pi c\ pbp_build G (prod `_` (P1 c) (_\ SP)) R1), pbp-cast G R1 RC.
% an exists of the goal: its witness is a new evar
pbp_build (app [{{ @ex }}, T, fun N T1 B]) (app [{{ @ex }}, _, fun NP _ BP])
    (app [{{ @pbp_ex_intro }}, T, fun N T1 B, WN, W, RC]) :- !,
  pbp-evar NP N T WN W, (pi c\ pbp_build (B W) (BP c) R1), pbp-cast (B W) R1 RC.

/* Connectives */
pbp_build {{ lp:P /\ _ }} {{ lp:P1 /\ lp:uvar }} 
    {{ conj lp:R1 _}} :- 
  pbp_build P P1 R1.
pbp_build {{ _ /\ lp:P }} {{ lp:uvar /\ lp:P1 }} 
    {{ conjR lp:R1 _}} :- 
  pbp_build P P1 R1.
pbp_build {{ lp:P \/ _ }} {{ lp:P1 \/ lp:uvar }} 
    {{ or_introl lp:R1}} :- !,
  pbp_build P P1 R1.
pbp_build {{ _ \/ lp:P }} {{ lp:uvar \/ lp:P1 }} 
    {{ or_intror lp:R1}} :- !,
  pbp_build P P1 R1.
pbp_build {{lp:P /\ _ -> lp:S }} {{lp:P1 /\ lp:X -> lp:uvar}} 
  {{and1imp lp:R}}
    :- 
  get_name X H, !, 
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  R = fun H _  (_\ R1).
pbp_build {{_ /\ lp:P -> lp:S }} {{lp:X /\ lp:P1 -> lp:uvar}} 
  {{and2imp lp:R}}
    :- 
  get_name X H, !, 
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  R = fun H _  (_\ R1).
pbp_build {{lp:P \/ _ -> lp:S }} {{lp:P1 \/ lp:X -> lp:uvar}} 
  {{or1imp lp:R1 lp:Z}}  :- 
  get_name X H, !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (_\ _).
pbp_build {{_ \/ lp:P -> lp:S }} {{lp:X \/ lp:P1 -> lp:uvar}} 
  {{or2imp lp:R1 lp:Z}} :- 
  get_name X H, !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (_\ _).
pbp_build {{(lp:P -> _) -> _ }} {{(lp:P1 -> lp:X) -> lp:uvar}} 
  {{imp1imp lp:T lp:T1}} :- 
  get_name X H, !,
  pbp_build P P1 T,
  T1 = fun H _  (_\ _).
pbp_build {{(_ -> lp:P) -> lp:R}} {{(lp:uvar -> lp:P1) -> lp:uvar}} 
  {{imp2imp lp:T _}} :-
  pbp_build {{lp:P -> lp:R}} {{lp:P1 -> _}} T.
pbp_build {{~  lp:P }} {{~ lp:P1 }} R :-
  pbp_build {{lp:P -> False}} {{ lp:P1 -> _ }} R.
pbp_build {{(~  lp:P) -> _ }} {{~ lp:P1 -> lp:uvar }} R :-
  pbp_build P P1 R1,
  R = {{negimp lp:R1}}.


pred pbp2_build i:term, i:term, o:term.
/* Binders, two selections: the rules of one selection, and those of an
   assumption in front of another assumption or of the goal.  The
   invertible ones first (the foralls of the goal introduced, the exists
   assumptions destructured), then the witnesses of the exists of the
   goal, then the instances of the forall assumptions: an evar may use the
   variables introduced before it, and a link may set a witness to an
   instance or an instance to a variable */
pbp2_build (prod N A F) (prod NP AP FP) (fun Name A R1) :- not (has-sel AP), !,
  pbp-intro-name NP AP N A F Name,
  pi x\ decl x Name A => pbp_bound Name A => pbp2_build (F x) (FP x) (R1 x).
% A -> forall x, F x, the type of x holding no selection: x is introduced
% (A -> B -> F, B a proposition: impimp1)
pbp2_build (prod H A (_\ prod N T F)) (prod _ AP (_\ prod NP TP FP)) R :-
  not (has-sel TP), !,
  pbp-intro-name NP TP N T F Name,
  (pi x\ decl x Name T => pbp_bound Name T => sigma G R1\ G = prod H A (_\ F x),
     pbp2_build G (prod `_` AP (_\ FP x)) R1, pbp-cast G R1 (RC x)),
  (pbp-quant T F, !, R = (app [{{ @pbp_impforall }}, A, T, fun N T F, fun Name T RC]) ;
   Fn = fun Name T RC, R = {{ impimp1 lp:Fn }}).
% (exists x, P x) -> S: destructured
pbp2_build (prod H (app [{{ @ex }}, T, fun N T1 P]) (_\ S))
           (prod _ (app [{{ @ex }}, _, fun NP _ P1]) (_\ SP))
    (app [{{ @pbp_existsimp }}, T, fun N T1 P, S, fun Name T RC]) :- !,
  pbp-exists-name NP N Name,
  pi x\ decl x Name T => pbp_bound Name T => sigma G R1\ G = prod H (P x) (_\ S),
    pbp2_build G (prod `_` (P1 x) (_\ SP)) R1, pbp-cast G R1 (RC x).
% A -> (exists x, P x) -> S: the second assumption is destructured
pbp2_build (prod H A (_\ prod H2 (app [{{ @ex }}, T, fun N T1 P]) (_\ S)))
           (prod _ AP (_\ prod _ (app [{{ @ex }}, _, fun NP _ P1]) (_\ SP)))
    (app [{{ @pbp_impexistsimp }}, A, T, fun N T1 P, S, fun Name T RC]) :- !,
  pbp-exists-name NP N Name,
  pi x\ decl x Name T => pbp_bound Name T => sigma G R1\ G = prod H A (_\ prod H2 (P x) (_\ S)),
    pbp2_build G (prod `_` AP (_\ prod `_` (P1 x) (_\ SP))) R1,
    pbp-cast G R1 (RC x).
% A -> exists x, F x: the witness is a new evar
pbp2_build (prod H A (_\ app [{{ @ex }}, T, fun N T1 F]))
           (prod _ AP (_\ app [{{ @ex }}, _, fun NP _ FP]))
    (app [{{ @pbp_impexists }}, A, T, fun N T1 F, WN, W, RC]) :- !,
  pbp-evar NP N T WN W, G = prod H A (_\ F W),
  (pi c\ pbp2_build G (prod `_` AP (_\ FP c)) R1), pbp-cast G R1 RC.
% exists x, F x: the witness is a new evar
pbp2_build (app [{{ @ex }}, T, fun N T1 B]) (app [{{ @ex }}, _, fun NP _ BP])
    (app [{{ @pbp_ex_intro }}, T, fun N T1 B, WN, W, RC]) :- !,
  pbp-evar NP N T WN W, (pi c\ pbp2_build (B W) (BP c) R1), pbp-cast (B W) R1 RC.
% (forall x, P x) -> S: used at a new evar
pbp2_build (prod H (prod N T P) (_\ S)) (prod _ (prod NP _ P1) (_\ SP))
    (app [{{ @pbp_forallimp }}, T, fun N T P, S, WN, W, RC]) :-
  pbp-quant T P, !,
  pbp-evar NP N T WN W, G = prod H (P W) (_\ S),
  (pi c\ pbp2_build G (prod `_` (P1 c) (_\ SP)) R1), pbp-cast G R1 RC.
% A -> (forall x, P x) -> S: the second assumption is used at a new evar
pbp2_build (prod H A (_\ prod H2 (prod N T P) (_\ S)))
           (prod _ AP (_\ prod _ (prod NP _ P1) (_\ SP)))
    (app [{{ @pbp_impforallimp }}, A, T, fun N T P, S, WN, W, RC]) :-
  pbp-quant T P, !,
  pbp-evar NP N T WN W, G = prod H A (_\ prod H2 (P W) (_\ S)),
  (pi c\ pbp2_build G (prod `_` AP (_\ prod `_` (P1 c) (_\ SP))) R1), pbp-cast G R1 RC.

/* Connectives */
/* Two active assumptions */
pbp2_build {{ lp:P /\ _ -> lp:R -> lp:S }} {{ lp:P1 /\ lp:X -> lp:R1 -> lp:uvar }} 
    {{and1impimp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R -> lp:S }} {{ lp:P1 -> lp:R1 -> _ }} T1,
  T = fun H _ (_\ T1). 
pbp2_build {{ _ /\ lp:P -> lp:R -> lp:S }} {{ lp:X /\ lp:P1 -> lp:R1 -> lp:uvar }} 
    {{and2impimp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R -> lp:S }} {{ lp:P1 -> lp:R1 -> _ }} T1,
  T = fun H _ (_\ T1). 
pbp2_build {{ lp:R -> lp:P /\ _ -> lp:S }} {{ lp:R1 -> lp:P1 /\ lp:X -> lp:uvar }} 
    {{impand1imp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T1,
  T = fun H _ (_\ T1). 
pbp2_build {{ lp:R -> _ /\ lp:P -> lp:S }} {{ lp:R1 -> lp:X /\ lp:P1 -> lp:uvar }} 
    {{impand2imp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T1,
  T = fun H _ (_\ T1). 
pbp2_build {{ lp:P \/ _ -> lp:R -> lp:S }} {{ lp:P1 \/ lp:X -> lp:R1 -> lp:uvar }} 
    {{or1impimp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R -> lp:S }} {{ lp:P1 -> lp:R1 -> _ }} T,
  T1 = fun H _ _. 
pbp2_build {{ _ \/ lp:P -> lp:R -> lp:S }} {{ lp:X \/ lp:P1 -> lp:R1 -> lp:uvar }} 
    {{or2impimp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R -> lp:S }} {{ lp:P1 -> lp:R1 -> _ }} T,
  T1 = fun H _ _. 
pbp2_build {{ lp:R -> lp:P \/ _ -> lp:S }} {{ lp:R1 -> lp:P1 \/ lp:X -> lp:uvar }} 
    {{impor1imp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T,
  T1 = fun H _ _. 
pbp2_build {{ lp:R -> _ \/ lp:P -> lp:S }} {{ lp:R1 -> lp:X \/ lp:P1 -> lp:uvar }} 
    {{impor2imp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T,
  T1 = fun H _ _. 

pbp2_build {{ (lp:P -> _) -> lp:R -> _ }} {{ (lp:P1 -> lp:X) -> lp:R1 -> lp:uvar }} 
    {{imp1impimp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P}} {{ lp:R1 -> lp:P1 }} T,
  T1 = fun H _ _. 
pbp2_build {{ (_ -> lp:P) -> lp:R -> lp:S }} {{ (lp:X -> lp:P1) -> lp:R1 -> lp:uvar }} 
    {{imp2impimp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R -> lp:S }} {{ lp:P1 -> lp:R1 -> _ }} T,
  T1 = fun H _ _. 
pbp2_build {{ lp:R -> (lp:P -> _) -> _ }} {{ lp:R1 -> (lp:P1 -> lp:X) -> lp:uvar }} 
    {{impimp1imp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P}} {{ lp:R1 -> lp:P1 }} T,
  T1 = fun H _ _. 
pbp2_build {{ lp:R -> (_ -> lp:P) -> lp:S }} {{ lp:R1 -> (lp:uvar -> lp:P1) -> lp:uvar }} 
    {{impimp2imp lp:T _}} :- 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T1, T = fun _ _ (_\ T1).
pbp2_build {{ ~  lp:P -> lp:R -> _ }} {{ ~ lp:P1 -> lp:R1 -> lp:uvar }} 
    {{negimpimp lp:T}} :- 
  pbp2_build {{ lp:R -> lp:P}} {{ lp:R1 -> lp:P1 }} T.
pbp2_build {{ lp:P -> ~ lp:R -> _}} {{ lp:P1 -> ~ lp:R1 -> lp:uvar }} 
    {{impnegimp lp:T}} :- 
  pbp2_build {{ lp:P -> lp:R }} {{ lp:P1 -> lp:R1 }} T. 

/* one active assumption and one active goal */

pbp2_build {{lp:P /\ _ -> lp:R }} {{lp:P1 /\ lp:X -> lp:R1}} 
    {{ and1imp lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T,
  T1 = fun H _ (_\T).
pbp2_build {{_ /\ lp:P -> lp:R }} {{lp:X /\ lp:P1 -> lp:R1}} 
    {{ and2imp lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T,
  T1 = fun H _ (_\T).
pbp2_build {{lp:P -> lp:R /\ _ }} {{lp:P1 -> lp:R1 /\ lp:uvar }} 
    {{ impand1 lp:T _}} :- 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T.
pbp2_build {{lp:P -> _ /\ lp:R }} {{lp:P1 -> lp:uvar /\ lp:R1}} 
    {{ impand2 lp:T _}} :- 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T.
pbp2_build {{lp:P \/ _ -> lp:R }} {{lp:P1 \/ lp:X -> lp:R1}} 
    {{ or1imp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T,
  T1 = fun H _ _.
pbp2_build {{_ \/ lp:P -> lp:R }} {{lp:X \/ lp:P1 -> lp:R1}} 
    {{ or2imp lp:T lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T,
  T1 = fun H _ _.
pbp2_build {{lp:P -> lp:R \/ _ }} {{lp:P1 -> lp:R1 \/ lp:uvar }} 
    {{ impor1 lp:T}} :- 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T.
pbp2_build {{lp:P -> _ \/ lp:R }} {{lp:P1 -> lp:uvar \/ lp:R1}} 
    {{ impor2 lp:T}} :- 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T.
pbp2_build {{lp:P -> _ -> lp:R }} {{lp:P1 -> lp:X -> lp:R1}} 
    {{impimp1 lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T,
  T1 = fun H _ (_\ T).
pbp2_build {{(_ -> lp:P) -> lp:R }} {{(lp:uvar -> lp:P1) -> lp:R1}} 
    {{ imp2imp lp:T _}} :- 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T.
pbp2_build {{lp:P -> ~ lp:R }} {{(lp:P1) -> ~ lp:R1}} T :- 
  pbp2_build {{lp:P -> lp:R -> False}} {{lp:P1 -> lp:R1 -> _}} T.

/* Usual pbp rules */
pbp2_build {{ _ /\ lp:P }} {{ lp:uvar /\ lp:P1 }} 
    {{ conjR lp:R1 _}} :- 
  pbp2_build P P1 R1.
pbp2_build {{ lp:P \/ _ }} {{ lp:P1 \/ lp:uvar }} 
    {{ or_introl lp:R1}} :- !,
  pbp2_build P P1 R1.
pbp2_build {{ _ \/ lp:P }} {{ lp:uvar \/ lp:P1 }} 
    {{ or_intror lp:R1}} :- !,
  pbp2_build P P1 R1.
pbp2_build {{lp:P /\ _ -> lp:S }} {{lp:P1 /\ lp:X -> lp:S1}} 
  {{and1imp lp:R}} :- 
  get_name X H, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> lp:S1 }} R1,
  R = fun H _  (_\ R1).
pbp2_build {{_ /\ lp:P -> lp:S }} {{lp:X /\ lp:P1 -> lp:S1}} 
  {{and2imp lp:R}}
    :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> lp:S1}} R1,
  R = fun H _  (_\ R1).
pbp2_build {{lp:P /\ lp:Q -> lp:R }} {{lp:P1 /\ lp:Q1 -> lp:uvar}} 
  {{and2imp lp:R1}} :- 
  pbp2_build {{lp:P -> lp:Q -> lp:R}} {{lp:P1 -> lp:Q1 -> _}} R1.
pbp2_build {{lp:P \/ _ -> lp:S }} {{lp:P1 \/ lp:X -> lp:uvar}} 
  {{or1imp lp:R1 lp:Z}}  :- 
  get_name X H, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (_\ _).
pbp2_build {{(lp:P -> _) -> _ }} {{(lp:P1 -> lp:X) -> lp:uvar}} 
  {{imp1imp lp:R1 lp:Z}} :-
  get_name X H, !,
  pbp2_build P P1 R1,
  Z = fun H _  (_\ _).
pbp2_build {{~  lp:P }} {{~ lp:P1 }} R :-
  pbp2_build {{lp:P -> False}} {{ lp:P1 -> _ }} R.
pbp2_build {{(~  lp:P) -> _ }} {{~ lp:P1 -> _ }} R :-
  pbp2_build P P1 R1,
  R = {{negimp lp:R1}}.



pbp2_build {{ lp:P /\ _ }} {{ lp:P1 /\ lp:uvar }} 
    {{ conj lp:R1 _}} :- 
  pbp2_build P P1 R1.

pred get_name i: term o: name.
get_name uvar `pbp`.

pred mapply2 i: term  o: term -> term.
mapply2 (fun _ _  F) F.

% [pbp-link A B] the assumption A proves B: the same term, or, when one of
% them holds an evar (a witness, an instance), unifiable
pred pbp-link i:term, i:term.
pbp-link A A :- !.
pbp-link A B :- (not (ground_term A) ; not (ground_term B)), coq.unify-eq A B ok.

% [pbp-premise-name NP N Name] the name of the selected premise: the one
% written in the pattern (forall (H : X), _), else N
pred pbp-premise-name i:name, i:name, o:name.
pbp-premise-name NP _ NP :- pbp-named NP S, !, pbp-name-free S "premise".
pbp-premise-name _ N N.

% [pbp-refine R Ty G GL] the proof R of Ty (holes in it) solves the goal G,
% leaving the goals GL: the holes, then the evars left open (witnesses,
% instances), which pbp-name-evars names
pred pbp-refine i:term, i:term, i:goal, o:list sealed-goal.
pbp-refine R Ty (goal _ RawEv _ Ev _) GL :-
  coq.elaborate-skeleton R Ty T ok,
  rm-evar RawEv Ev,
  coq.ltac.collect-goals T GS SH,
  RawEv = T, Ev = T,
  pbp-name-evars T,
  std.append GS SH GL.

% [pbp-witness-lemma C I] the lemma C takes its witness marker as its
% argument number I (from 0)
pred pbp-witness-lemma i:constant, o:int.
pbp-witness-lemma C I :- coq.gref->id (const C) S, pbp-witness-arg S I.

pred pbp-witness-arg i:string, o:int.
pbp-witness-arg "pbp_ex_intro" 2.
pbp-witness-arg "pbp_forallimp" 3.
pbp-witness-arg "pbp_impforallimp" 4.
pbp-witness-arg "pbp_impexists" 3.

% [pbp-name-evars T] the witnesses of T that are evars are named after
% their markers (pbp-evar), Rocq's way: ?n, ?n0 if ?n is taken
pred pbp-name-evars i:term.
pbp-name-evars (app [global (const C) | As]) :- pbp-witness-lemma C I, !,
  std.drop I As L, L = [fun N _ _, W | _], pbp-name-witness N W,
  std.forall As pbp-name-evars.
pbp-name-evars (app L) :- !, std.forall L pbp-name-evars.
pbp-name-evars (prod _ T F) :- !, pbp-name-evars T, pi x\ pbp-name-evars (F x).
pbp-name-evars (fun _ T F) :- !, pbp-name-evars T, pi x\ pbp-name-evars (F x).
pbp-name-evars (let _ T B F) :- !, pbp-name-evars T, pbp-name-evars B,
  pi x\ pbp-name-evars (F x).
pbp-name-evars (match T R L) :- !, pbp-name-evars T, pbp-name-evars R,
  std.forall L pbp-name-evars.
pbp-name-evars _.

% [pbp-name-witness N W] the witness W, if it is an evar, is named N
pred pbp-name-witness i:name, i:term.
pbp-name-witness N W :- var W, !, coq.name->id N S0,
  rex.replace "^pbp_evar_" "" S0 S,
  (coq.ltac.fresh-goal-name S S1, coq.ltac.name-uvar W S1, ! ; true).
pbp-name-witness _ _.

pred pbp_scan i:int, i:term o:term o:goal o: list sealed-goal.
pbp_scan 0 (F as (fun _ _ x\ fun _ _ _)) Ty G GL :- !,
  pi x\pi y\sigma T2\
  coq.mk-app F [x, y] T2,
  pbp_sel x => pbp_sel y =>
  (pi A B\ pbp2_build (prod _ A (_\ B)) {{lp:x -> lp:y}}  (fun `pbp` _ (x\x)) :- pbp-link A B) =>
  (pi A B\ pbp2_build (prod _ A (_\ B)) {{lp:y -> lp:x}}  (fun `pbp` _ (x\x)) :- pbp-link A B) =>
  (pbp2_build Ty T2 R, 
   pbp-refine R Ty G GL).
pbp_scan 0 (fun N _ S) Ty G GL :- !,
     pi x \  
          pbp_sel x =>
          pbp_build _ x _ => 
          (pi NP Name\ pbp_build (prod _ _ _) (prod NP x _) (fun Name _ _) :- pbp-premise-name NP N Name) =>
          (pi A B NP Name\ pbp_build (prod _ A (_\ B)) (prod NP x _) (fun Name _ (x\x)) :-
             pbp-link A B, pbp-premise-name NP N Name) =>
     (pbp_build Ty (S x) R, 
       pbp-refine R Ty G GL).
pbp_scan N (fun Na _ S) Ty G GL :- !,
     N1 is N - 1, 
     pi x \  get_name x Na => 
          pbp_scan N1 (S x) Ty G GL.
}}.

Elpi Tactic pbp_tac.
Elpi Accumulate Db pbp_build.db.
Elpi Accumulate lp:{{
  solve (goal Ctx _ Ty _ [open-trm N F] as G) GL :-
  % (the context, for the names already used: pbp-name-free)
  pbp_ctx Ctx =>
  pbp_scan N F Ty G GL.
}}.

Tactic Notation "pbp" uconstr(t) :=
  elpi pbp_tac ltac_open_term:(t).

Lemma test_pbp0 (A B C : Prop) : A /\ B -> B /\ A.
Proof.
pbp [Z in  _ -> _ /\ Z].
move: pbp.
by pbp [X in X /\ _ -> _].
move: pbp.
by pbp [X in Y /\ X -> _].
Qed.

Lemma test_pbp1 (A B C : Prop) : A /\ B -> A /\ B.
Proof.
pbp  [ X Y in  X /\ Z -> Y /\ _].
move: Z.
pbp  [ X Y in  X -> _ -> Y].
Qed.

Lemma test_pbp2 (A B C : Prop) : A \/ B -> A\/ B.
Proof.
pbp  [ X in  X \/ Y -> _].
by pbp [X in X \/ _].
by pbp [X in _ \/ X].
Qed.

Lemma test_pbp3 (A B C : Prop) : A \/ B -> B \/ A.
Proof.
pbp  [ X Y in  X \/ Z -> _ \/ Y].
move: Z.
pbp  [ X Y in  X  -> Y \/ _].
Qed.

Lemma test_pbp4 (A B : Prop) : (B -> A) -> B -> A.
Proof.
by pbp  [X Y in (_ -> X) -> H -> Y].
Qed.

Lemma test_pbp5 (A B : Prop) : (B -> A) -> B -> A.
Proof.
pbp  [X Y in (X -> H) -> Y -> _].
move: H.
pbp  [X Y in X -> _ -> Y].
Qed.

Lemma test_pb6 (A B : Prop) : (A -> B) /\ A -> B.
Proof.
pbp  [X Y in (X -> H) /\ Y -> _].
move: H.
pbp  [X Y in X -> _ -> Y].
Qed.

(* Three links that the rules allow (opposite polarities) *)

(* the mirror of the left case: linking under the right disjunct *)
Lemma test_pbp7 (A C : Prop) : C \/ (A -> A).
Proof.
by pbp [X Y in _ \/ (X -> Y)].
Qed.

(* linking inside the premise of a premise *)
Lemma test_pbp8 (B D : Prop) : ((D -> D) -> B) -> B.
Proof.
pbp [X Y in ((X -> Y) -> _) -> _].
by [].   (* the link leaves the premise B as a hypothesis *)
Qed.

(* rule M12: the second A is under a premise of an assumption *)
Lemma test_pbp9 (A D : Prop) : A -> (A -> (A -> D)) -> D.
Proof.
pbp [X Y in X -> (_ -> (Y -> _)) -> _].
  by move=> _.   (* the link gives D *)
by [].           (* the premise left: A -> A *)
Qed.
