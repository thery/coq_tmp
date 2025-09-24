From Stdlib Require Import ssreflect.
From elpi Require Import elpi.

(*
Goal forall A B, A /\ B -> B.
intros A B.
case H; apply: swapf2; intros C D.
Show Proof.
*)

Definition conjR {A B : Prop} (X : A) (Y : B) := conj Y X.

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
pbp_build {{lp:P -> _}} {{lp:P1 -> lp:uvar}} 
    {{ fun Hp => lp:(R1 Hp)}} :- !,
  pbp_buildf P P1 R1.
pred pbp_buildf i:term, i:term, o:term -> term.
pbp_buildf {{ lp:P /\ _ }} {{ lp:P1 /\ lp:uvar }} 
  (hp \ {{ match lp:hp with conj x _ => 
       lp:{{R1 {{x}}}} end}}) :-
  pbp_buildf P P1 R1.
pbp_buildf {{ _ /\ lp:P }} {{ lp:uvar /\ lp:P1 }} 
  (hp \ {{ match lp:hp with conj _ x => lp:{{R1 {{x}}}} end}}) :-
  pbp_buildf P P1 R1.
}}.

Elpi Tactic pbp_tac.
Elpi Accumulate Db pbp_build.db.
Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ [trm (fun _ _ S)] as G) GL :- 
  coq.say Ty,
  pi x \  pbp_build _ x _ => 
          pbp_buildf _ x (a\ _) =>
     (pbp_build Ty (S x) R, 
       coq.elaborate-skeleton R Ty T ok,
       coq.say "ff " R, refine.no_check T G GL).
}}.

Tactic Notation "pbp" uconstr(t) :=
  elpi pbp_tac ltac_term:(t).

Lemma test_pbp : (1 = 1 /\ 2 = 2) /\ (3 = 3 /\ 4 =4) -> 5=5.
pbp  (fun X =>  (_ /\ (_ /\ X) -> _)).
Abort.
