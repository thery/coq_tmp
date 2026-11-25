(* Tests of pbp_pattern (pbp_select.v): from a selection in the printed
   goal to the pbp call.

   [elpi pbp_pattern_expect Line Ws Sel ...] checks that pbp_pattern gives
   the line Line for the selections Sel (Ws: the subterms that selections
   were widened to, "" for none); a selection ["P"] is the subterm at
   path P of the conclusion, ["H" "P"] the one of the type of the
   hypothesis H.  The line is then run.  The patterns of pbp.v's tests are compared to the hand-written
   ones: the two proofs are the same term. *)

From Stdlib Require Import ssreflect PeanoNat List.
From Stdlib Require Utf8.
From elpi Require Import elpi.
From coq_tmp Require Import pbp_select.

(* ---------- Arithmetic: the two occurrences of a and of b ---------- *)

(* a + b = b + a is @eq nat (a + b) (b + a): a is 2.1 and 3.2, b is 2.2
   and 3.1 *)
Goal forall a b : nat, a + b = b + a.
Proof.
move=> a b.
elpi pbp_pattern_expect "pbp [X in X + _ = _]." "" "2.1".
elpi pbp_pattern_expect "pbp [X in _ = _ + X]." "" "3.2".
elpi pbp_pattern_expect "pbp [X in _ + X = _]." "" "2.2".
elpi pbp_pattern_expect "pbp [X in _ = X + _]." "" "3.1".
elpi pbp_pattern_expect "pbp [X in X = _]." "" "2".
(* pbp has no rule for =, but the patterns are ssreflect's: rewriting at
   the pattern shows the occurrence it denotes *)
rewrite -[X in X + _ = _]Nat.add_0_r.
lazymatch goal with |- (a + 0) + b = b + a => idtac end.
rewrite -[X in _ = _ + X]Nat.add_0_r.
lazymatch goal with |- (a + 0) + b = b + (a + 0) => idtac end.
rewrite -[X in _ + X = _]Nat.add_0_r.
lazymatch goal with |- (a + 0) + (b + 0) = b + (a + 0) => idtac end.
rewrite -[X in _ = X + _]Nat.add_0_r.
lazymatch goal with |- (a + 0) + (b + 0) = (b + 0) + (a + 0) => idtac end.
by rewrite Nat.add_comm.
Qed.

(* ---------- A left-nested sum ---------- *)

(* a + b + c = c is (a + b) + c = c: a + b is 2.1 *)
Goal forall a b c : nat, a + b + c = c.
Proof.
move=> a b c.
elpi pbp_pattern_expect "pbp [X in X + _ = _]." "" "2.1".
Abort.

(* ---------- The tests of pbp.v: hand-written and produced patterns ------ *)

(* Each test of pbp.v is proved twice: [_hand] is pbp.v's script, [_gen]
   uses the patterns that pbp_pattern produces (where pbp.v names an
   assumption with a free variable, the produced pattern has _, and the
   assumption is called pbp).  The two proofs are the same term. *)

Lemma test_pbp0_hand (A B C : Prop) : A /\ B -> B /\ A.
Proof.
pbp [Z in  _ -> _ /\ Z].
move: pbp.
by pbp [X in X /\ _ -> _].
move: pbp.
by pbp [X in Y /\ X -> _].
Defined.

(* A/\B->B/\A *)
Lemma test_pbp0_gen (A B C : Prop) : A /\ B -> B /\ A.
Proof.
elpi pbp_pattern_expect "pbp [X in _ -> _ /\ X]." "" "2.2".
pbp [X in _ -> _ /\ X].
move: pbp.
elpi pbp_pattern_expect "pbp [X in X /\ _ -> _]." "" "1.1".
by pbp [X in X /\ _ -> _].
move: pbp.
elpi pbp_pattern_expect "pbp [X in _ /\ X -> _]." "" "1.2".
by pbp [X in _ /\ X -> _].
Defined.

Check (eq_refl : test_pbp0_gen = test_pbp0_hand).

Lemma test_pbp1_hand (A B C : Prop) : A /\ B -> A /\ B.
Proof.
pbp  [ X Y in  X /\ Z -> Y /\ _].
move: Z.
pbp  [ X Y in  X -> _ -> Y].
Defined.

(* A/\B->A/\B, then B->A->B *)
Lemma test_pbp1_gen (A B C : Prop) : A /\ B -> A /\ B.
Proof.
elpi pbp_pattern_expect "pbp [X Y in X /\ _ -> Y /\ _]." "" "1.1" "2.1".
pbp [X Y in X /\ _ -> Y /\ _].
move: pbp.
elpi pbp_pattern_expect "pbp [X Y in X -> _ -> Y]." "" "1" "2.2".
pbp [X Y in X -> _ -> Y].
Defined.

Check (eq_refl : test_pbp1_gen = test_pbp1_hand).

Lemma test_pbp2_hand (A B C : Prop) : A \/ B -> A\/ B.
Proof.
pbp  [ X in  X \/ Y -> _].
by pbp [X in X \/ _].
by pbp [X in _ \/ X].
Defined.

(* A\/B->A\/B, then A\/B twice *)
Lemma test_pbp2_gen (A B C : Prop) : A \/ B -> A\/ B.
Proof.
elpi pbp_pattern_expect "pbp [X in X \/ _ -> _]." "" "1.1".
pbp [X in X \/ _ -> _].
elpi pbp_pattern_expect "pbp [X in X \/ _]." "" "1".
by pbp [X in X \/ _].
elpi pbp_pattern_expect "pbp [X in _ \/ X]." "" "2".
by pbp [X in _ \/ X].
Defined.

Check (eq_refl : test_pbp2_gen = test_pbp2_hand).

Lemma test_pbp3_hand (A B C : Prop) : A \/ B -> B \/ A.
Proof.
pbp  [ X Y in  X \/ Z -> _ \/ Y].
move: Z.
pbp  [ X Y in  X  -> Y \/ _].
Defined.

(* A\/B->B\/A, then B->B\/A *)
Lemma test_pbp3_gen (A B C : Prop) : A \/ B -> B \/ A.
Proof.
elpi pbp_pattern_expect "pbp [X Y in X \/ _ -> _ \/ Y]." "" "1.1" "2.2".
pbp [X Y in X \/ _ -> _ \/ Y].
move: pbp.
elpi pbp_pattern_expect "pbp [X Y in X -> Y \/ _]." "" "1" "2.1".
pbp [X Y in X -> Y \/ _].
Defined.

Check (eq_refl : test_pbp3_gen = test_pbp3_hand).

Lemma test_pbp4_hand (A B : Prop) : (B -> A) -> B -> A.
Proof.
by pbp  [X Y in (_ -> X) -> H -> Y].
Defined.

(* (B->A)->B->A *)
Lemma test_pbp4_gen (A B : Prop) : (B -> A) -> B -> A.
Proof.
elpi pbp_pattern_expect "pbp [X Y in (_ -> X) -> _ -> Y]." "" "1.2" "2.2".
by pbp [X Y in (_ -> X) -> _ -> Y].
Defined.

Check (eq_refl : test_pbp4_gen = test_pbp4_hand).

Lemma test_pbp5_hand (A B : Prop) : (B -> A) -> B -> A.
Proof.
pbp  [X Y in (X -> H) -> Y -> _].
move: H.
pbp  [X Y in X -> _ -> Y].
Defined.

(* (B->A)->B->A, then A->B->A *)
Lemma test_pbp5_gen (A B : Prop) : (B -> A) -> B -> A.
Proof.
elpi pbp_pattern_expect "pbp [X Y in (X -> _) -> Y -> _]." "" "1.1" "2.1".
pbp [X Y in (X -> _) -> Y -> _].
move: pbp.
elpi pbp_pattern_expect "pbp [X Y in X -> _ -> Y]." "" "1" "2.2".
pbp [X Y in X -> _ -> Y].
Defined.

Check (eq_refl : test_pbp5_gen = test_pbp5_hand).

Lemma test_pb6_hand (A B : Prop) : (A -> B) /\ A -> B.
Proof.
pbp  [X Y in (X -> H) /\ Y -> _].
move: H.
pbp  [X Y in X -> _ -> Y].
Defined.

(* (A->B)/\A->B, then B->A->B *)
Lemma test_pb6_gen (A B : Prop) : (A -> B) /\ A -> B.
Proof.
elpi pbp_pattern_expect "pbp [X Y in (X -> _) /\ Y -> _]." "" "1.1.1" "1.2".
pbp [X Y in (X -> _) /\ Y -> _].
move: pbp.
elpi pbp_pattern_expect "pbp [X Y in X -> _ -> Y]." "" "1" "2.2".
pbp [X Y in X -> _ -> Y].
Defined.

Check (eq_refl : test_pb6_gen = test_pb6_hand).

(* Two selections must be apart: the first B (1.1) is inside the goal ("") *)
Goal forall A B : Prop, (B -> A) -> B -> A.
Proof.
move=> A B.
Fail elpi pbp_pattern "1.1" "".
Abort.

(* ---------- Notations: lists ---------- *)

(* x::l1++l2=(x::l1)++l2 *)
Goal forall (x : nat) (l1 l2 : list nat), x :: l1 ++ l2 = (x :: l1) ++ l2.
Proof.
move=> x l1 l2.
elpi pbp_pattern_expect "pbp [X in X :: _ = _]." "" "2.2".
elpi pbp_pattern_expect "pbp [X in _ :: X ++ _ = _]." "" "2.3.2".
elpi pbp_pattern_expect "pbp [X in _ :: X = _]." "" "2.3".
elpi pbp_pattern_expect "pbp [X in _ = X ++ _]." "" "3.2".
elpi pbp_pattern_expect "pbp [X in _ = (_ :: X) ++ _]." "" "3.2.3".
elpi pbp_pattern_expect "pbp [X in X = _]." "" "2".
rewrite -[X in _ = X ++ _]app_nil_r.
lazymatch goal with |- x :: l1 ++ l2 = ((x :: l1) ++ nil) ++ l2 => idtac end.
by rewrite app_nil_r.
Qed.

(* ListNotations' [x] and pbp's [X in ...] are incompatible notations
   (Rocq warns of it): with ListNotations, the pattern is not parsed *)
Module ListNotationsClash.
Import ListNotations.
Goal forall x : nat, [x] ++ [] = [x].
Proof.
move=> x.
Fail elpi pbp_pattern "2.2.2".
Abort.
End ListNotationsClash.

(* ---------- Implicit arguments ---------- *)

(* length(revl)=lengthl: the type argument of length, rev and = is not
   printed; the head length, applied to it, is not a printed subterm *)
Goal forall (A : Type) (l : list A), length (rev l) = length l.
Proof.
move=> A l.
elpi pbp_pattern_expect "pbp [X in length X = _]." "" "2.2".
elpi pbp_pattern_expect "pbp [X in length (rev X) = _]." "" "2.2.2".
elpi pbp_pattern_expect "pbp [X in _ = length X]." "" "3.2".
rewrite -[X in length X = _]app_nil_r.
lazymatch goal with |- length (rev l ++ nil) = length l => idtac end.
by rewrite app_nil_r length_rev.
Qed.

(* ---------- Binders ---------- *)

(* foralln:nat,existsm:nat,n+m=m+n: a selection that uses bound variables
   is the variable of the pattern applied to them *)
Goal forall n : nat, exists m : nat, n + m = m + n.
Proof.
elpi pbp_pattern_expect "pbp [X in forall n : nat, exists m : nat, X n + _ = _]." "" "2.2.2.2.1".
elpi pbp_pattern_expect "pbp [X in forall n : nat, exists m : nat, _ + X m = _]." "" "2.2.2.2.2".
elpi pbp_pattern_expect "pbp [X in forall n : nat, exists m : nat, X n m = _]." "" "2.2.2.2".
elpi pbp_pattern_expect "pbp [X in forall n : nat, X n]." "" "2".
(* the type nat of n cannot be abstracted: n + m needs it; the selection
   is widened to the forall *)
elpi pbp_pattern_expect "pbp [X in X]." "forall n : nat, exists m : nat, n + m = m + n" "1".
Abort.

(* ---------- Hypotheses ---------- *)

(* a selection in a hypothesis H generalizes it (move: H) and points in
   the premise *)
Goal forall A B : Prop, A /\ B -> B /\ A.
Proof.
move=> A B H.
elpi pbp_pattern_expect "move: H; pbp [X in X /\ _ -> _]." "" "H" "1".
move: H; pbp [X in X /\ _ -> _].
Abort.

(* Linking a hypothesis and the conclusion: back-chaining (the paper's
   A -> (A -> B) -> B, the B's linked) *)
Goal forall A B : Prop, A -> (A -> B) -> B.
Proof.
move=> A B a ab.
(* A->B *)
elpi pbp_pattern_expect "move: ab; pbp [X Y in (_ -> X) -> Y]." "" "ab" "2" "".
move: ab; pbp [X Y in (_ -> X) -> Y].
exact: a.
Qed.

(* Linking two hypotheses: forward chaining (the A's linked) *)
Goal forall A B : Prop, A -> (A -> B) -> B.
Proof.
move=> A B a ab.
elpi pbp_pattern_expect "move: a ab; pbp [X Y in X -> (Y -> _) -> _]."
  "" "a" "" "ab" "1".
(* the order of the selections does not change the generalization *)
elpi pbp_pattern_expect "move: a ab; pbp [X Y in Y -> (X -> _) -> _]."
  "" "ab" "1" "a" "".
move: a ab; pbp [X Y in X -> (Y -> _) -> _].
by move=> _.
Qed.

(* The variables of the pattern are bound by it: only the names its body
   uses are avoided (here the hypothesis X is not in the body) *)
Goal forall X Y : Prop, X /\ Y -> Y /\ X.
Proof.
move=> X Y.
elpi pbp_pattern_expect "pbp [X in X /\ _ -> _]." "" "1.1".
elpi pbp_pattern_expect "pbp [X Y in X /\ _ -> _ /\ Y]." "" "1.1" "2.2".
pbp [X0 Y0 in X0 /\ _ -> _ /\ Y0].
Abort.

(* ---------- Several goals, line breaks ---------- *)

Goal forall Alpha Beta Gamma Delta : Prop,
  Alpha \/ Beta \/ Gamma \/ Delta ->
  (Alpha \/ Beta \/ Gamma \/ Delta) \/ (Alpha \/ Beta \/ Gamma \/ Delta)
  \/ (Delta \/ Gamma \/ Beta \/ Alpha).
Proof.
move=> Alpha Beta Gamma Delta H.
(* printed on two lines; without blanks:
   (Alpha\/Beta\/Gamma\/Delta)\/(Alpha\/Beta\/Gamma\/Delta)\/Delta\/Gamma... *)
elpi pbp_pattern_expect "pbp [X in _ \/ _ \/ _ \/ X \/ _]." "" "2.2.2.1".
pbp [X in _ \/ _ \/ _ \/ X \/ _].
lazymatch goal with |- Gamma => idtac end.
Abort.

(* A goal selector: the call is for the goal it selects *)
Goal forall A B : Prop, A -> B -> A /\ B.
Proof.
move=> A B a b; split.
2: elpi pbp_pattern_expect "pbp [X in X]." "" "".
Abort.

(* ---------- Unicode notations ---------- *)

Module Unicode.
Import Utf8.

(* ∀ n : nat, n + 0 = n: a Unicode notation *)
Goal forall n : nat, n + 0 = n.
Proof.
elpi pbp_pattern_expect "pbp [X in ∀ n : nat, X n + _ = _]." "" "2.2.1".
elpi pbp_pattern_expect "pbp [X in ∀ n : nat, _ + X = _]." "" "2.2.2".
Abort.
End Unicode.

(* ---------- The scrutinee of an if or a match ---------- *)

(* with ssreflect imported, if c then a else b is printed by ssreflect's
   notation, whose text (if X then _ else _) elaborates: the plain pattern
   is kept, no type is added to X *)
Module IfMatch.
Notation "'IF' c 'THEN' a 'ELSE' b" := (if c then a else b) (at level 200).
(* (ifbthennelse0)=n: b is 3 *)
Goal forall (b : bool) (n : nat), (IF b THEN n ELSE 0) = n.
intros b n.
elpi pbp_pattern_expect "pbp [X in (if X then _ else _) = _]." "" "2.0".
Abort.
End IfMatch.

Goal forall (b : bool) (n : nat), (if b then n else 0) = n.
intros b n.
elpi pbp_pattern_expect "pbp [X in (if X then _ else _) = _]." "" "2.0".
Abort.

(* matchnwith|0=>true|S_=>falseend=true: n is 5 *)
Goal forall n : nat, match n with 0 => true | S _ => false end = true.
intros n.
elpi pbp_pattern_expect "pbp [X in match X with | 0 => _ | S _ => _ end = _]." "" "2.0".
Abort.
