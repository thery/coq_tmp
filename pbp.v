From Stdlib Require Import ssreflect.
From elpi Require Import elpi.

(*
Goal forall A B, A /\ B -> B.
intros A B.
case H; apply: swapf2; intros C D.
Show Proof.
*)

Definition conjR {A B : Prop} (X : A) (Y : B) := conj Y X.

Lemma impand1 {A B C : Prop} (H : B -> A -> C) : A /\ B -> C.
Proof. by move=> [H1 H2]; apply: H. Qed.
Lemma impand2 {A B C : Prop} (H : A -> B -> C) : A /\ B -> C.
Proof. by move=> [H1 H2]; apply: H. Qed.
Lemma impor1 {A B C : Prop} (H : A -> C) (H1 : B -> C) : A \/ B -> C.
Proof. by move=> [H2|H2]; [apply/H/H2 | apply/H1/H2]. Qed.
Lemma impor2 {A B C : Prop} (H : B -> C) (H1 : A -> C) : A \/ B -> C.
Proof. by move=> [H2|H2]; [apply/H1/H2 | apply/H/H2]. Qed.
Lemma impimp1 {A B C : Prop} (H1 : B -> C) (H : A) (H2 : A -> B) : C.
Proof. by apply/H1/H2. Qed.
Lemma impimp2 {A B C : Prop} (H : A) (H1 : B -> C) (H2 : A -> B) : C.
Proof. by apply/H1/H2. Qed.

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
pbp_build {{ _ -> lp:P }} {{ lp:uvar -> lp:P1 }} 
    {{ fun Hp => lp:R1}} :- !,
  pbp_build P P1 R1.
pbp_build {{lp:P /\ _ -> lp:S }} {{lp:P1 /\ lp:uvar -> lp:uvar}} 
  {{impand1 (fun Hp => lp:R1)}}
    :- !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1.
pbp_build {{_ /\ lp:P -> lp:S }} {{lp:uvar /\ lp:P1 -> lp:uvar}} 
  {{impand2 (fun Hp => lp:R1)}}
    :- !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1.
pbp_build {{lp:P \/ _ -> lp:S }} {{lp:P1 \/ lp:uvar -> lp:uvar}} 
  {{impor1 lp:R1 _}}
    :- !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1.
pbp_build {{_ \/ lp:P -> lp:S }} {{lp:uvar \/ lp:P1 -> lp:uvar}} 
  {{impor2 lp:R1 _}}
    :- !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1.
pbp_build {{(_ -> lp:P) -> lp:S }} {{(lp:uvar -> lp:P1) -> lp:uvar}} 
  {{impimp1 lp:R1 _}}
    :- !,
  pbp_build {{lp:P -> lp:S}} {{lp:P1 -> _}} R1.
pbp_build {{(lp:P -> _) -> lp:S }} {{(lp:P1 -> lp:uvar) -> lp:uvar}} 
  {{impimp2 lp:R1 (fun Hp => _)}}
    :- coq.say "dkdkkd" {{lp:P -> lp:S}} {{lp:P1 -> _}} !,
  pbp_build P P1 R1.
}}.

Elpi Tactic pbp_tac.
Elpi Accumulate Db pbp_build.db.
Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ [trm (fun _ _ S)] as G) GL :- 
  coq.say Ty,
  pi x \  pbp_build _ x _ => 
          pbp_build {{_ -> _}} {{lp:x -> lp:uvar}}  {{fun Hp => _}} =>
     (pbp_build Ty (S x) R, 
       coq.elaborate-skeleton R Ty T ok,
       coq.say "ff " R, refine.no_check T G GL).
}}.

Tactic Notation "pbp" uconstr(t) :=
  elpi pbp_tac ltac_term:(t).

Lemma test_pbp : ((1 = 1 /\ 2 = 2) -> (3 = 3 /\ 4 =4)) -> 5=5.
Proof.
pbp  (fun X => (_ -> (_ /\ X)) -> _) .
