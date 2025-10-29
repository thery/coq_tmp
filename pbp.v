From Stdlib Require Import ssreflect.
From elpi Require Import elpi.

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


Elpi Db pbp_build.db lp:{{

pred pbp_build i:term, i:term, o:term.
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
pbp_build {{ _ -> lp:P }} {{ lp:X -> lp:P1 }} R :-
  get_name X H, !, 
  pbp_build P P1 R1,
  R = fun H _  (x\ R1).
pbp_build {{lp:P /\ _ -> lp:S }} {{lp:P1 /\ lp:X -> lp:uvar}} 
  {{and1imp lp:R}}
    :- 
  get_name X H, !, 
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  R = fun H _  (x\ R1).
pbp_build {{_ /\ lp:P -> lp:S }} {{lp:X /\ lp:P1 -> lp:uvar}} 
  {{and2imp lp:R}}
    :- 
  get_name X H, !, 
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  R = fun H _  (x\ R1).
pbp_build {{lp:P \/ _ -> lp:S }} {{lp:P1 \/ lp:X -> lp:uvar}} 
  {{or1imp lp:R1 lp:Z}}  :- 
  get_name X H, !, !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (x\ _).
pbp_build {{_ \/ lp:P -> lp:S }} {{lp:X \/ lp:P1 -> lp:uvar}} 
  {{or2imp lp:R1 lp:Z}} :- 
  get_name X H, !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (x\ _).
pbp_build {{(lp:P -> _) -> _ }} {{(lp:P1 -> lp:X) -> lp:uvar}} 
  {{imp1imp lp:T lp:T1}} :- 
  get_name X H, !,
  pbp_build P P1 T,
  T1 = fun H _  (x\ _).
pbp_build {{(_ -> lp:P) -> lp:R}} {{(lp:uvar -> lp:P1) -> lp:uvar}} 
  {{imp2imp lp:T _}} :-
  pbp_build {{lp:P -> lp:R}} {{lp:P1 -> _}} T.
pbp_build {{~  lp:P }} {{~ lp:P1 }} R :-
  pbp_build {{lp:P -> False}} {{ lp:P1 -> _ }} R.
pbp_build {{(~  lp:P) -> _ }} {{~ lp:P1 -> lp:uvar }} R :-
  pbp_build P P1 R1,
  R = {{negimp lp:R1}}.


pred pbp2_build i:term, i:term, o:term.
/* Two active assumptions */
pbp2_build {{ lp:P /\ _ -> lp:R -> lp:S }} {{ lp:P1 /\ lp:X -> lp:R1 -> lp:uvar }} 
    {{and1impimp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R -> lp:S }} {{ lp:P1 -> lp:R1 -> _ }} T1,
  T = fun H _ (x\ T1). 
pbp2_build {{ _ /\ lp:P -> lp:R -> lp:S }} {{ lp:X /\ lp:P1 -> lp:R1 -> lp:uvar }} 
    {{and2impimp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R -> lp:S }} {{ lp:P1 -> lp:R1 -> _ }} T1,
  T = fun H _ (x\ T1). 
pbp2_build {{ lp:R -> lp:P /\ _ -> lp:S }} {{ lp:R1 -> lp:P1 /\ lp:X -> lp:uvar }} 
    {{impand1imp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T1,
  T = fun H _ (x\ T1). 
pbp2_build {{ lp:R -> _ /\ lp:P -> lp:S }} {{ lp:R1 -> lp:X /\ lp:P1 -> lp:uvar }} 
    {{impand2imp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T1,
  T = fun H _ (x\ T1). 
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
    {{impimp2imp lp:T1 _}} :- 
  pbp2_build {{ lp:R -> lp:P -> lp:S }} {{ lp:R1 -> lp:P1 -> _ }} T1.
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
  T1 = fun H _ (x\T).
pbp2_build {{_ /\ lp:P -> lp:R }} {{lp:X /\ lp:P1 -> lp:R1}} 
    {{ and2imp lp:T1}} :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:R}} {{lp:P1 -> lp:R1}} T,
  T1 = fun H _ (x\T).
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
  T1 = fun H _ (x\ T).
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
  pbp_build P P1 R1.
pbp2_build {{ _ -> lp:P }} {{ lp:X -> lp:P1 }} R :-
  get_name X H, !, 
  pbp2_build P P1 R1,
  R = fun H _  (x\ R1).
pbp2_build {{lp:P /\ _ -> lp:S }} {{lp:P1 /\ lp:X -> lp:S1}} 
  {{and1imp lp:R}} :- 
  get_name X H, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> lp:S1 }} R1,
  R = fun H _  (x\ R1).
pbp2_build {{_ /\ lp:P -> lp:S }} {{lp:X /\ lp:P1 -> lp:S1}} 
  {{and2imp lp:R}}
    :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> lp:S1}} R1,
  R = fun H _  (x\ R1).
pbp2_build {{lp:P /\ lp:Q -> lp:R }} {{lp:P1 /\ lp:Q1 -> lp:uvar}} 
  {{and2imp lp:R1}} :- 
  pbp2_build {{lp:P -> lp:Q -> lp:R}} {{lp:P1 -> lp:Q1 -> _}} R1.
pbp2_build {{lp:P \/ _ -> lp:S }} {{lp:P1 \/ lp:X -> lp:uvar}} 
  {{or1imp lp:R1 lp:Z}}  :- 
  get_name X H, !, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (x\ _).
pbp_build {{_ \/ lp:P -> lp:S }} {{lp:X \/ lp:P1 -> lp:uvar}} 
  {{or2imp lp:R1 lp:Z}} :- 
  get_name X H, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (x\ _).
pbp2_build {{(lp:P -> _) -> lp:S }} {{(lp:P1 -> lp:X) -> lp:uvar}} 
  {{imp1imp lp:R1 _}} :-
  get_name X H, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1.
pbp2_build {{(lp:P -> _) -> _ }} {{(lp:P1 -> lp:X) -> lp:uvar}} 
  {{imp2imp lp:R1 lp:Z}} :-
  get_name X H, !,
  pbp2_build P P1 R1,
  Z = fun H _  (x\ _).
pbp2_build {{~  lp:P }} {{~ lp:P1 }} R :-
  pbp2_build {{lp:P -> False}} {{ lp:P1 -> _ }} R.
pbp2_build {{(~  lp:P) -> _ }} {{~ lp:P1 -> _ }} R :-
  pbp2_build P P1 R1,
  R = {{negimp lp:R1}}.

pbp2_build {{ lp:P -> _ -> lp:R }} {{ lp:P1 -> lp:X -> lp:R1 }} 
    {{imp1imp lp:T}} :- 
  get_name X H, !, 
  pbp2_build {{ lp:P -> lp:R }} {{ lp:P1 -> lp:R1 }} T1,
  T = fun H _ (x\ T1). 


pbp2_build {{ lp:P /\ _ }} {{ lp:P1 /\ lp:uvar }} 
    {{ conj lp:R1 _}} :- 
  pbp2_build P P1 R1.
pbp2_build {{ _ /\ lp:P }} {{ lp:uvar /\ lp:P1 }} 
    {{ conjR lp:R1 _}} :- 
  pbp2_build P P1 R1.
pbp2_build {{ lp:P \/ _ }} {{ lp:P1 \/ lp:uvar }} 
    {{ or_introl lp:R1}} :- !,
  pbp2_build P P1 R1.
pbp2_build {{ _ \/ lp:P }} {{ lp:uvar \/ lp:P1 }} 
    {{ or_intror lp:R1}} :- !,
  pbp_build P P1 R1.
pbp2_build {{ _ -> lp:P }} {{ lp:X -> lp:P1 }} R :-
  get_name X H, !, 
  pbp2_build P P1 R1,
  R = fun H _  (x\ R1).
pbp2_build {{lp:P /\ _ -> lp:S }} {{lp:P1 /\ lp:X -> lp:uvar}} 
  {{and1imp lp:R}}
    :- 
  get_name X H, !, 
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  R = fun H _  (x\ R1).
pbp2_build {{_ /\ lp:P -> lp:S }} {{lp:X /\ lp:P1 -> lp:uvar}} 
  {{and2imp lp:R}}
    :- 
  get_name X H, !, 
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  R = fun H _  (x\ R1).
pbp2_build {{lp:P \/ _ -> lp:S }} {{lp:P1 \/ lp:X -> lp:uvar}} 
  {{or1imp lp:R1 lp:Z}}  :- 
  get_name X H, !, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (x\ _).
pbp_build {{_ \/ lp:P -> lp:S }} {{lp:X \/ lp:P1 -> lp:uvar}} 
  {{or2imp lp:R1 lp:Z}} :- 
  get_name X H, !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1,
  Z = fun H _  (x\ _).
pbp2_build {{(_ -> lp:P) -> lp:S }} {{(lp:uvar -> lp:P1) -> lp:uvar}} 
  {{impimp1 lp:R1 _}}
    :- !,
  pbp2_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1.
pbp2_build {{(lp:P -> _) -> _ }} {{(lp:P1 -> lp:X) -> lp:uvar}} 
  {{imp2imp lp:R1 lp:Z}} :-
  get_name X H, !,
  pbp2_build P P1 R1,
  Z = fun H _  (x\ _).
pbp2_build {{~  lp:P }} {{~ lp:P1 }} R :-
  pbp2_build {{lp:P -> False}} {{ lp:P1 -> _ }} R.
pbp2_build {{(~  lp:P) -> _ }} {{~ lp:P1 -> _ }} R :-
  pbp2_build P P1 R1,
  R = {{negimp lp:R1}}.

pred get_name i: term o: name.
get_name uvar `pbp`.

pred mapply2 i: term  o: term -> term.
mapply2 (fun _ _  F) F.

pred pbp_scan i:int, i:term o:term o:goal o: list sealed-goal.
pbp_scan 0 (F as (fun _ _ x\ fun _ _ _)) Ty G GL :- !,
  pi x\pi y\sigma T2\
  coq.mk-app F [x, y] T2,
  pbp2_build {{lp:X -> lp:X}} {{lp:x -> lp:y}}  (fun N _ (x\x)) =>
  pbp2_build {{lp:X -> lp:X}} {{lp:y -> lp:x}}  (fun N _ (x\x)) =>
  (pbp2_build Ty T2 R, 
   coq.elaborate-skeleton R Ty T ok,
   refine.no_check T G GL).
pbp_scan 0 (fun N _ S) Ty G GL :- !,
     pi x \  
          pbp_build _ x _ => 
          pbp_build {{_ -> _}} {{lp:x -> _}}  (fun N _ _) =>
          pbp_build {{lp:X -> lp:X}} {{lp:x -> _}}  (fun N _ (x\x)) =>
     (pbp_build Ty (S x) R, 
       coq.elaborate-skeleton R Ty T ok,
       refine.no_check T G GL).
pbp_scan N (fun Na _ S) Ty G GL :- !,
     N1 is N - 1, 
     pi x \  get_name x Na => 
          pbp_scan N1 (S x) Ty G GL.
}}.

Elpi Tactic pbp_tac.
Elpi Accumulate Db pbp_build.db.
Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ [open-trm N F] as G) GL :- 
  pbp_scan N F Ty G GL.
}}.

Notation "'[' x .. y 'in' p ']' " :=
  ( (fun x => .. ( (fun y => p)) ..))
  (x binder, y binder, right associativity).

Tactic Notation "pbp" uconstr(t) :=
  elpi pbp_tac ltac_open_term:(t).

Lemma test_pbp0 (A B C : Prop) : A /\ B -> A /\ B.
Proof.
pbp  [ X in  X /\ Y -> _].
by pbp [X in X /\ _].
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

Lemma test_pbp3 (A B C : Prop) : A \/ B -> A \/ B.
Proof.
pbp  [ X Y in  X \/ Z -> Y \/ _].
move: Z.
pbp  [ X Y in  X  -> _ \/ Y].
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
