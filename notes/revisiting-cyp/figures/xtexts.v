(* The texts of xtext shown in the note; make.sh compiles this file with
   -Q . Fig and keeps what it prints in xtexts.out. *)
From Stdlib Require Import Arith.
From XText Require Import ExtractText.

(* praeclarum, the term of "Extracting Text from Proofs" (xtext/paper.v) *)
Definition praeclarum : forall x y z t : Prop,
  (x -> z) /\ (y -> t) -> x /\ y -> z /\ t :=
  fun x y z t h1 h2 =>
    and_ind (fun (i : x -> z) (j : y -> t) =>
      and_ind (fun (k : x) (l : y) => conj (i k) (j l)) h2) h1.

ExtractText praeclarum.
#[tags] ExtractText praeclarum.
ExtractText praeclarum to "praeclarum_xtext.md".
ExtractText praeclarum to "praeclarum_ar.md" in "ar".

(* a proof in progress: stopped after split, the first conjunct done *)
Lemma praeclarum_partial (x y z t : Prop) : (x -> z) /\ (y -> t) -> x /\ y -> z /\ t.
Proof. intros [Hxz Hyt] [Hx Hy]. split. apply Hxz. exact Hx.
ExtractText_partial.

(* the drinker's principle, as in xtext/paper.v *)
From Stdlib Require Import Classical.
Lemma drinker (A : Set) (P : A -> Prop) (y : A) :
  exists x : A, P x -> forall z : A, P z.
Proof.
  destruct (classic (forall z : A, P z)) as [H|H].
  - exists y. intros _. exact H.
  - destruct (not_all_ex_not A P H) as [t i].
    exists t. intros h. destruct (i h).
Qed.
ExtractText drinker to "drinker.md".
