(* Differential corpus: 200 random goals (seed 42), written by
   gen_random.sh; each one gets 12 random patterns (random_gen.v). *)
From Stdlib Require Import List.
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support random_gen.
Import ListNotations.
Section Random.
Variables (f : nat -> nat -> nat) (g : nat -> nat).

Goal forall (a b c : nat) (l : list nat), c = (length l) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.1" "1" ltac_term:(G)) | idtac "SSR	rand.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in _ = X); elpi z_report "rand.1" "2" ltac_term:(G)) | idtac "SSR	rand.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.1" "3" ltac_term:(G)) | idtac "SSR	rand.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in _ = X); elpi z_report "rand.1" "4" ltac_term:(G)) | idtac "SSR	rand.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l as X in c = X); elpi z_report "rand.1" "5" ltac_term:(G)) | idtac "SSR	rand.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in _ = X); elpi z_report "rand.1" "6" ltac_term:(G)) | idtac "SSR	rand.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in c = X); elpi z_report "rand.1" "7" ltac_term:(G)) | idtac "SSR	rand.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c = X); elpi z_report "rand.1" "8" ltac_term:(G)) | idtac "SSR	rand.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l in X in c = X); elpi z_report "rand.1" "9" ltac_term:(G)) | idtac "SSR	rand.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "rand.1" "10" ltac_term:(G)) | idtac "SSR	rand.1	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in _ = X); elpi z_report "rand.1" "11" ltac_term:(G)) | idtac "SSR	rand.1	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.1" "12" ltac_term:(G)) | idtac "SSR	rand.1	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g ((fst (0, (f b c))) + ((snd (2, 3)) * (1 + c)))) = 
(fst ((f (snd ((3 * 0), b)) (f (f a a) (snd (b, c)))), 3)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.2" "1" ltac_term:(G)) | idtac "SSR	rand.2	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in snd X); elpi z_report "rand.2" "2" ltac_term:(G)) | idtac "SSR	rand.2	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.2" "3" ltac_term:(G)) | idtac "SSR	rand.2	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (fst (0, f b c) + snd (2, 3) * (X + c)) = fst (f (snd (3 * 0, b)) (f (f a a) (snd (b, c))), 3)); elpi z_report "rand.2" "4" ltac_term:(G)) | idtac "SSR	rand.2	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (f (snd (3 * 0, b)) (f (f a a) (snd (b, c))), X)); elpi z_report "rand.2" "5" ltac_term:(G)) | idtac "SSR	rand.2	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (2, 3) * X); elpi z_report "rand.2" "6" ltac_term:(G)) | idtac "SSR	rand.2	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g (fst (0, f b c) + X * (1 + _))); elpi z_report "rand.2" "7" ltac_term:(G)) | idtac "SSR	rand.2	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.2" "8" ltac_term:(G)) | idtac "SSR	rand.2	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (2, 3) * (X + c)); elpi z_report "rand.2" "9" ltac_term:(G)) | idtac "SSR	rand.2	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X * (1 + c)); elpi z_report "rand.2" "10" ltac_term:(G)) | idtac "SSR	rand.2	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in g (fst (0, f b c) + X)); elpi z_report "rand.2" "11" ltac_term:(G)) | idtac "SSR	rand.2	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.2" "12" ltac_term:(G)) | idtac "SSR	rand.2	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (b + ((g c) + (g 0))) = 
(snd ((f (snd ((3 * c), (g c))) (length l)), ((g (fst (a, 1))) + (f (fst (3, b)) (f 0 3))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (g c + g 0) = snd (f (snd (S (S X) * c, g c)) _, g (fst (a, 1)) + f (fst (3, b)) (f 0 3))); elpi z_report "rand.3" "1" ltac_term:(G)) | idtac "SSR	rand.3	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (f (snd (3 * c, g c)) (length l), g (fst (a, X)) + f (fst (3, b)) (f 0 3))); elpi z_report "rand.3" "2" ltac_term:(G)) | idtac "SSR	rand.3	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (f (snd (3 * c, g c)) (length l), g (fst (a, X)) + f (fst (3, b)) (f 0 3))); elpi z_report "rand.3" "3" ltac_term:(G)) | idtac "SSR	rand.3	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (f (snd (3 * c, g c)) (length l), g (fst (a, 1)) + f (fst (3, b)) (f _ (S X)))); elpi z_report "rand.3" "4" ltac_term:(G)) | idtac "SSR	rand.3	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f X (f 0 3)); elpi z_report "rand.3" "5" ltac_term:(G)) | idtac "SSR	rand.3	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (f (snd (3 * c, g c)) (length l), g (fst (a, 1)) + f (fst (3, b)) (f 0 (S (S X))))); elpi z_report "rand.3" "6" ltac_term:(G)) | idtac "SSR	rand.3	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (fst (3, b)) (f _ (S (S X)))); elpi z_report "rand.3" "7" ltac_term:(G)) | idtac "SSR	rand.3	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (f (snd (3 * c, g c)) (length l), g (fst (a, 1)) + f (fst (3, b)) (f _ (S (S X))))); elpi z_report "rand.3" "8" ltac_term:(G)) | idtac "SSR	rand.3	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in (f (snd (3 * c, g c)) (length l), g (fst (a, 1)) + f (fst (S (S X), b)) (f 0 3))); elpi z_report "rand.3" "9" ltac_term:(G)) | idtac "SSR	rand.3	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b + (g c + g 0) = snd (f (snd (3 * c, g c)) (length _), g (fst (_, X)) + f (fst (3, b)) (f 0 3))); elpi z_report "rand.3" "10" ltac_term:(G)) | idtac "SSR	rand.3	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.3" "11" ltac_term:(G)) | idtac "SSR	rand.3	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.3" "12" ltac_term:(G)) | idtac "SSR	rand.3	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (f 2 (f a c)) = 
(f (f ((g 0) * (b * c)) (g (3 + 3))) (fst ((snd (3, a)), (length l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in fst X); elpi z_report "rand.4" "1" ltac_term:(G)) | idtac "SSR	rand.4	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in f 2 (f a c) = f (f (g 0 * (b * c)) (g (3 + 3))) (fst (snd (3, a), X))); elpi z_report "rand.4" "2" ltac_term:(G)) | idtac "SSR	rand.4	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _ in X in f (f (g 0 * (b * c)) (g (3 + 3))) X); elpi z_report "rand.4" "3" ltac_term:(G)) | idtac "SSR	rand.4	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _); elpi z_report "rand.4" "4" ltac_term:(G)) | idtac "SSR	rand.4	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.4" "5" ltac_term:(G)) | idtac "SSR	rand.4	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l in X in (snd (3, a), X)); elpi z_report "rand.4" "6" ltac_term:(G)) | idtac "SSR	rand.4	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in f (f (g 0 * (b * c)) (g (3 + 3))) (fst (snd (3, a), X))); elpi z_report "rand.4" "7" ltac_term:(G)) | idtac "SSR	rand.4	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.4" "8" ltac_term:(G)) | idtac "SSR	rand.4	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in f (f (g 0 * (b * c)) (g (3 + 3))) X); elpi z_report "rand.4" "9" ltac_term:(G)) | idtac "SSR	rand.4	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.4" "10" ltac_term:(G)) | idtac "SSR	rand.4	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.4" "11" ltac_term:(G)) | idtac "SSR	rand.4	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l); elpi z_report "rand.4" "12" ltac_term:(G)) | idtac "SSR	rand.4	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length ((b * (length l)) :: l)) = 
b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in X = _); elpi z_report "rand.5" "1" ltac_term:(G)) | idtac "SSR	rand.5	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l); elpi z_report "rand.5" "2" ltac_term:(G)) | idtac "SSR	rand.5	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l in X in length X = b); elpi z_report "rand.5" "3" ltac_term:(G)) | idtac "SSR	rand.5	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in length (b * X :: l) = _); elpi z_report "rand.5" "4" ltac_term:(G)) | idtac "SSR	rand.5	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ in X in length X); elpi z_report "rand.5" "5" ltac_term:(G)) | idtac "SSR	rand.5	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in length X); elpi z_report "rand.5" "6" ltac_term:(G)) | idtac "SSR	rand.5	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in b * X); elpi z_report "rand.5" "7" ltac_term:(G)) | idtac "SSR	rand.5	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b * X :: l); elpi z_report "rand.5" "8" ltac_term:(G)) | idtac "SSR	rand.5	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length (b * X :: l)); elpi z_report "rand.5" "9" ltac_term:(G)) | idtac "SSR	rand.5	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l); elpi z_report "rand.5" "10" ltac_term:(G)) | idtac "SSR	rand.5	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in b * X); elpi z_report "rand.5" "11" ltac_term:(G)) | idtac "SSR	rand.5	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in b * X :: _); elpi z_report "rand.5" "12" ltac_term:(G)) | idtac "SSR	rand.5	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 1 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in X = 1); elpi z_report "rand.6" "1" ltac_term:(G)) | idtac "SSR	rand.6	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S _ = X); elpi z_report "rand.6" "2" ltac_term:(G)) | idtac "SSR	rand.6	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ = X); elpi z_report "rand.6" "3" ltac_term:(G)) | idtac "SSR	rand.6	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 = X); elpi z_report "rand.6" "4" ltac_term:(G)) | idtac "SSR	rand.6	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in 1 = X); elpi z_report "rand.6" "5" ltac_term:(G)) | idtac "SSR	rand.6	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = X); elpi z_report "rand.6" "6" ltac_term:(G)) | idtac "SSR	rand.6	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 1 = X); elpi z_report "rand.6" "7" ltac_term:(G)) | idtac "SSR	rand.6	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "rand.6" "8" ltac_term:(G)) | idtac "SSR	rand.6	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X = 1); elpi z_report "rand.6" "9" ltac_term:(G)) | idtac "SSR	rand.6	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in 1 = X); elpi z_report "rand.6" "10" ltac_term:(G)) | idtac "SSR	rand.6	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.6" "11" ltac_term:(G)) | idtac "SSR	rand.6	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.6" "12" ltac_term:(G)) | idtac "SSR	rand.6	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((fst (b, ((3 * c) * (g a)))) + a) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in fst X); elpi z_report "rand.7" "1" ltac_term:(G)) | idtac "SSR	rand.7	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (b, 3 * c * X)); elpi z_report "rand.7" "2" ltac_term:(G)) | idtac "SSR	rand.7	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in S _ = X); elpi z_report "rand.7" "3" ltac_term:(G)) | idtac "SSR	rand.7	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in 1 = fst (b, 3 * _ * X) + a); elpi z_report "rand.7" "4" ltac_term:(G)) | idtac "SSR	rand.7	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in 3 * c * X); elpi z_report "rand.7" "5" ltac_term:(G)) | idtac "SSR	rand.7	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a); elpi z_report "rand.7" "6" ltac_term:(G)) | idtac "SSR	rand.7	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g _ as X in (b, 3 * c * X)); elpi z_report "rand.7" "7" ltac_term:(G)) | idtac "SSR	rand.7	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in fst (_, 3 * c * X)); elpi z_report "rand.7" "8" ltac_term:(G)) | idtac "SSR	rand.7	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in fst (b, X) + a); elpi z_report "rand.7" "9" ltac_term:(G)) | idtac "SSR	rand.7	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (b, 3 * c * X)); elpi z_report "rand.7" "10" ltac_term:(G)) | idtac "SSR	rand.7	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in fst X + a); elpi z_report "rand.7" "11" ltac_term:(G)) | idtac "SSR	rand.7	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 * c * X); elpi z_report "rand.7" "12" ltac_term:(G)) | idtac "SSR	rand.7	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
(2 + ((snd ((fst (b, c)), (length l))) * (snd ((1 + 3), (3 * 2))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (1 + 3, S (S X) * 2)); elpi z_report "rand.8" "1" ltac_term:(G)) | idtac "SSR	rand.8	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.8" "2" ltac_term:(G)) | idtac "SSR	rand.8	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.8" "3" ltac_term:(G)) | idtac "SSR	rand.8	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in c = 2 + X); elpi z_report "rand.8" "4" ltac_term:(G)) | idtac "SSR	rand.8	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 1 + X); elpi z_report "rand.8" "5" ltac_term:(G)) | idtac "SSR	rand.8	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in (X, 3 * 2)); elpi z_report "rand.8" "6" ltac_term:(G)) | idtac "SSR	rand.8	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + S (S X)); elpi z_report "rand.8" "7" ltac_term:(G)) | idtac "SSR	rand.8	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.8" "8" ltac_term:(G)) | idtac "SSR	rand.8	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in (S _ + S (S X), 3 * 2)); elpi z_report "rand.8" "9" ltac_term:(G)) | idtac "SSR	rand.8	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ = 2 + snd (fst (b, c), length l) * snd (X + 3, 3 * 2)); elpi z_report "rand.8" "10" ltac_term:(G)) | idtac "SSR	rand.8	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (1 + 3, S (S X) * 2)); elpi z_report "rand.8" "11" ltac_term:(G)) | idtac "SSR	rand.8	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S X + snd (fst (b, c), length l) * snd (1 + 3, 3 * 2)); elpi z_report "rand.8" "12" ltac_term:(G)) | idtac "SSR	rand.8	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = (f (3 + b) c) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X) + _); elpi z_report "rand.9" "1" ltac_term:(G)) | idtac "SSR	rand.9	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.9" "2" ltac_term:(G)) | idtac "SSR	rand.9	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + _); elpi z_report "rand.9" "3" ltac_term:(G)) | idtac "SSR	rand.9	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (S (S X) + b) c); elpi z_report "rand.9" "4" ltac_term:(G)) | idtac "SSR	rand.9	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.9" "5" ltac_term:(G)) | idtac "SSR	rand.9	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.9" "6" ltac_term:(G)) | idtac "SSR	rand.9	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (S X + _) c); elpi z_report "rand.9" "7" ltac_term:(G)) | idtac "SSR	rand.9	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in S X); elpi z_report "rand.9" "8" ltac_term:(G)) | idtac "SSR	rand.9	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.9" "9" ltac_term:(G)) | idtac "SSR	rand.9	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in f (S (S X) + _) _); elpi z_report "rand.9" "10" ltac_term:(G)) | idtac "SSR	rand.9	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S (S X)); elpi z_report "rand.9" "11" ltac_term:(G)) | idtac "SSR	rand.9	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b = f (S (S X) + _) c); elpi z_report "rand.9" "12" ltac_term:(G)) | idtac "SSR	rand.9	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (a :: ((fst (a, b)) :: (l ++ l)))) = 1 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (a :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "1" ltac_term:(G)) | idtac "SSR	rand.10	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length (a :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "2" ltac_term:(G)) | idtac "SSR	rand.10	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (a :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "3" ltac_term:(G)) | idtac "SSR	rand.10	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.10" "4" ltac_term:(G)) | idtac "SSR	rand.10	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.10" "5" ltac_term:(G)) | idtac "SSR	rand.10	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (a :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "6" ltac_term:(G)) | idtac "SSR	rand.10	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in length (_ :: fst (a, b) :: _) = X); elpi z_report "rand.10" "7" ltac_term:(G)) | idtac "SSR	rand.10	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (_ :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "8" ltac_term:(G)) | idtac "SSR	rand.10	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (a :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "9" ltac_term:(G)) | idtac "SSR	rand.10	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in length (a :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "10" ltac_term:(G)) | idtac "SSR	rand.10	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (a :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "11" ltac_term:(G)) | idtac "SSR	rand.10	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (_ :: fst (a, b) :: l ++ l) = X); elpi z_report "rand.10" "12" ltac_term:(G)) | idtac "SSR	rand.10	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
(length (((c :: l) ++ l) ++ ((1 :: l) ++ l))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X :: l); elpi z_report "rand.11" "1" ltac_term:(G)) | idtac "SSR	rand.11	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (((c :: l) ++ l) ++ (X :: l) ++ _)); elpi z_report "rand.11" "2" ltac_term:(G)) | idtac "SSR	rand.11	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in ((c :: l) ++ l) ++ X); elpi z_report "rand.11" "3" ltac_term:(G)) | idtac "SSR	rand.11	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in a = length (((c :: l) ++ l) ++ (X :: l) ++ l)); elpi z_report "rand.11" "4" ltac_term:(G)) | idtac "SSR	rand.11	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X :: _); elpi z_report "rand.11" "5" ltac_term:(G)) | idtac "SSR	rand.11	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in X ++ _); elpi z_report "rand.11" "6" ltac_term:(G)) | idtac "SSR	rand.11	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (((c :: l) ++ l) ++ (X :: l) ++ _)); elpi z_report "rand.11" "7" ltac_term:(G)) | idtac "SSR	rand.11	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in ((c :: l) ++ l) ++ X ++ l); elpi z_report "rand.11" "8" ltac_term:(G)) | idtac "SSR	rand.11	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (((c :: l) ++ l) ++ X)); elpi z_report "rand.11" "9" ltac_term:(G)) | idtac "SSR	rand.11	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length (((c :: l) ++ l) ++ X)); elpi z_report "rand.11" "10" ltac_term:(G)) | idtac "SSR	rand.11	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length X); elpi z_report "rand.11" "11" ltac_term:(G)) | idtac "SSR	rand.11	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in ((c :: l) ++ l) ++ X); elpi z_report "rand.11" "12" ltac_term:(G)) | idtac "SSR	rand.11	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g b) = a .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g b in X in X = _); elpi z_report "rand.12" "1" ltac_term:(G)) | idtac "SSR	rand.12	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b in X in X = a); elpi z_report "rand.12" "2" ltac_term:(G)) | idtac "SSR	rand.12	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in X = _); elpi z_report "rand.12" "3" ltac_term:(G)) | idtac "SSR	rand.12	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X = _); elpi z_report "rand.12" "4" ltac_term:(G)) | idtac "SSR	rand.12	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b in X in X = a); elpi z_report "rand.12" "5" ltac_term:(G)) | idtac "SSR	rand.12	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.12" "6" ltac_term:(G)) | idtac "SSR	rand.12	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.12" "7" ltac_term:(G)) | idtac "SSR	rand.12	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g _); elpi z_report "rand.12" "8" ltac_term:(G)) | idtac "SSR	rand.12	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b); elpi z_report "rand.12" "9" ltac_term:(G)) | idtac "SSR	rand.12	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b in X in X = a); elpi z_report "rand.12" "10" ltac_term:(G)) | idtac "SSR	rand.12	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X = _); elpi z_report "rand.12" "11" ltac_term:(G)) | idtac "SSR	rand.12	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b as X in X = a); elpi z_report "rand.12" "12" ltac_term:(G)) | idtac "SSR	rand.12	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (g c)) * a) = 
((g (fst ((snd (c, a)), (g 0)))) + (g (fst ((snd (2, c)), b)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in g (fst (snd (c, a), g 0)) + g (fst (snd (S X, _), b))); elpi z_report "rand.13" "1" ltac_term:(G)) | idtac "SSR	rand.13	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.13" "2" ltac_term:(G)) | idtac "SSR	rand.13	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.13" "3" ltac_term:(G)) | idtac "SSR	rand.13	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.13" "4" ltac_term:(G)) | idtac "SSR	rand.13	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst (snd X, b)); elpi z_report "rand.13" "5" ltac_term:(G)) | idtac "SSR	rand.13	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g (fst (snd (c, a), g 0)) + g (fst (snd (X, c), _))); elpi z_report "rand.13" "6" ltac_term:(G)) | idtac "SSR	rand.13	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in (S X, c)); elpi z_report "rand.13" "7" ltac_term:(G)) | idtac "SSR	rand.13	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in g (fst (snd (c, a), g 0)) + X); elpi z_report "rand.13" "8" ltac_term:(G)) | idtac "SSR	rand.13	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.13" "9" ltac_term:(G)) | idtac "SSR	rand.13	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.13" "10" ltac_term:(G)) | idtac "SSR	rand.13	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.13" "11" ltac_term:(G)) | idtac "SSR	rand.13	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (S X, c)); elpi z_report "rand.13" "12" ltac_term:(G)) | idtac "SSR	rand.13	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((f (fst (b, a)) (fst (b, 1))), ((a * b) * 1))) * (fst ((length (l ++ l)), (f (length l) (length l))))) 
= ((g ((length l) + (g 1))) * (((g b) + (2 + 0)) * ((g a) * (b * 0)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ * _ in X in g a * X); elpi z_report "rand.14" "1" ltac_term:(G)) | idtac "SSR	rand.14	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * 0); elpi z_report "rand.14" "2" ltac_term:(G)) | idtac "SSR	rand.14	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * _ as X in fst (f (fst (b, a)) (fst (b, 1)), a * b * 1) * fst (length (l ++ l), f (length l) (length l)) = g (length l + g 1) * ((g b + (2 + 0)) * (g _ * X))); elpi z_report "rand.14" "3" ltac_term:(G)) | idtac "SSR	rand.14	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in g a * X); elpi z_report "rand.14" "4" ltac_term:(G)) | idtac "SSR	rand.14	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * 0 in X in fst (f (fst (b, a)) (fst (b, 1)), a * b * 1) * fst (length (l ++ l), f (length l) (length l)) = g (length l + g 1) * ((g b + (2 + 0)) * X)); elpi z_report "rand.14" "5" ltac_term:(G)) | idtac "SSR	rand.14	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * _ in X in g (length l + g 1) * X); elpi z_report "rand.14" "6" ltac_term:(G)) | idtac "SSR	rand.14	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (g b + (2 + 0)) * (g a * X)); elpi z_report "rand.14" "7" ltac_term:(G)) | idtac "SSR	rand.14	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "rand.14" "8" ltac_term:(G)) | idtac "SSR	rand.14	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * 0 in X in g a * X); elpi z_report "rand.14" "9" ltac_term:(G)) | idtac "SSR	rand.14	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * _ as X in g a * X); elpi z_report "rand.14" "10" ltac_term:(G)) | idtac "SSR	rand.14	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * 0); elpi z_report "rand.14" "11" ltac_term:(G)) | idtac "SSR	rand.14	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ * _ in X in g _ * X); elpi z_report "rand.14" "12" ltac_term:(G)) | idtac "SSR	rand.14	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = (f a 3) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.15" "1" ltac_term:(G)) | idtac "SSR	rand.15	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.15" "2" ltac_term:(G)) | idtac "SSR	rand.15	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.15" "3" ltac_term:(G)) | idtac "SSR	rand.15	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f _ X); elpi z_report "rand.15" "4" ltac_term:(G)) | idtac "SSR	rand.15	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.15" "5" ltac_term:(G)) | idtac "SSR	rand.15	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.15" "6" ltac_term:(G)) | idtac "SSR	rand.15	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f _ (S X)); elpi z_report "rand.15" "7" ltac_term:(G)) | idtac "SSR	rand.15	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in length l = f a (S (S X))); elpi z_report "rand.15" "8" ltac_term:(G)) | idtac "SSR	rand.15	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.15" "9" ltac_term:(G)) | idtac "SSR	rand.15	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length l = f _ X); elpi z_report "rand.15" "10" ltac_term:(G)) | idtac "SSR	rand.15	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in S (S X)); elpi z_report "rand.15" "11" ltac_term:(G)) | idtac "SSR	rand.15	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l = f _ (S (S X))); elpi z_report "rand.15" "12" ltac_term:(G)) | idtac "SSR	rand.15	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 
(snd (((0 * (3 * a)) * ((snd (1, 0)) * 1)), (f (snd ((fst (0, 2)), 3)) (fst ((snd (1, b)), a))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in 3 = snd (0 * (3 * a) * (snd (1, 0) * 1), f (snd (X, 3)) (fst (snd (1, b), a)))); elpi z_report "rand.16" "1" ltac_term:(G)) | idtac "SSR	rand.16	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.16" "2" ltac_term:(G)) | idtac "SSR	rand.16	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.16" "3" ltac_term:(G)) | idtac "SSR	rand.16	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in snd (1, 0) * X); elpi z_report "rand.16" "4" ltac_term:(G)) | idtac "SSR	rand.16	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in (X, _)); elpi z_report "rand.16" "5" ltac_term:(G)) | idtac "SSR	rand.16	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.16" "6" ltac_term:(G)) | idtac "SSR	rand.16	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.16" "7" ltac_term:(G)) | idtac "SSR	rand.16	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in 3 = snd (0 * (3 * a) * (snd (1, 0) * 1), f (snd (fst (0, 2), 3)) (fst (snd (X, _), _)))); elpi z_report "rand.16" "8" ltac_term:(G)) | idtac "SSR	rand.16	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in 3 = snd (0 * (3 * a) * (snd (1, _) * 1), f (snd (fst (0, 2), 3)) (fst (snd (X, _), a)))); elpi z_report "rand.16" "9" ltac_term:(G)) | idtac "SSR	rand.16	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ * (S (S X) * _) * (snd (1, 0) * 1)); elpi z_report "rand.16" "10" ltac_term:(G)) | idtac "SSR	rand.16	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = snd (0 * (3 * a) * (snd (1, 0) * 1), f (snd (fst (0, 2), 3)) (fst (snd (1, b), a)))); elpi z_report "rand.16" "11" ltac_term:(G)) | idtac "SSR	rand.16	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (0 * (3 * a) * (snd (1, 0) * 1), f (snd (fst (_, X), 3)) (fst (snd (1, b), a)))); elpi z_report "rand.16" "12" ltac_term:(G)) | idtac "SSR	rand.16	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (2 + 0)) * (g (g (0 + 1)))) = 
2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.17" "1" ltac_term:(G)) | idtac "SSR	rand.17	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (2 + 0) * g (g (0 + X))); elpi z_report "rand.17" "2" ltac_term:(G)) | idtac "SSR	rand.17	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.17" "3" ltac_term:(G)) | idtac "SSR	rand.17	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (g (0 + X))); elpi z_report "rand.17" "4" ltac_term:(G)) | idtac "SSR	rand.17	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.17" "5" ltac_term:(G)) | idtac "SSR	rand.17	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in g X * g (g (0 + 1))); elpi z_report "rand.17" "6" ltac_term:(G)) | idtac "SSR	rand.17	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.17" "7" ltac_term:(G)) | idtac "SSR	rand.17	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (_ + X)); elpi z_report "rand.17" "8" ltac_term:(G)) | idtac "SSR	rand.17	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in S X); elpi z_report "rand.17" "9" ltac_term:(G)) | idtac "SSR	rand.17	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in g (2 + 0) * g (g (0 + 1)) = S X); elpi z_report "rand.17" "10" ltac_term:(G)) | idtac "SSR	rand.17	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X); elpi z_report "rand.17" "11" ltac_term:(G)) | idtac "SSR	rand.17	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in g (2 + 0) * g (g (0 + X))); elpi z_report "rand.17" "12" ltac_term:(G)) | idtac "SSR	rand.17	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (f (fst ((snd (c, c)), (snd (a, a)))) ((length l) + (length l))) (length l)) 
= (fst ((fst ((snd ((length l), (length l))), 2)), 0)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.18" "1" ltac_term:(G)) | idtac "SSR	rand.18	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.18" "2" ltac_term:(G)) | idtac "SSR	rand.18	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (snd (length l, length l), S X)); elpi z_report "rand.18" "3" ltac_term:(G)) | idtac "SSR	rand.18	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f (f (fst (snd (c, c), snd (a, a))) (length l + length l)) (length l) = fst (fst (snd (length l, length l), X), 0)); elpi z_report "rand.18" "4" ltac_term:(G)) | idtac "SSR	rand.18	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (f (fst (snd (c, c), snd (a, a))) (length l + length l)) _ = fst (fst (snd (length l, length l), S X), 0)); elpi z_report "rand.18" "5" ltac_term:(G)) | idtac "SSR	rand.18	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (snd (length l, length l), S X)); elpi z_report "rand.18" "6" ltac_term:(G)) | idtac "SSR	rand.18	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in S X); elpi z_report "rand.18" "7" ltac_term:(G)) | idtac "SSR	rand.18	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.18" "8" ltac_term:(G)) | idtac "SSR	rand.18	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.18" "9" ltac_term:(G)) | idtac "SSR	rand.18	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f (fst (snd (c, c), snd (a, a))) (length l + length l)) (length l) = fst (fst (snd (length l, length l), S X), 0)); elpi z_report "rand.18" "10" ltac_term:(G)) | idtac "SSR	rand.18	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.18" "11" ltac_term:(G)) | idtac "SSR	rand.18	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (snd (length l, length l), S X)); elpi z_report "rand.18" "12" ltac_term:(G)) | idtac "SSR	rand.18	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 1 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 = X); elpi z_report "rand.19" "1" ltac_term:(G)) | idtac "SSR	rand.19	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.19" "2" ltac_term:(G)) | idtac "SSR	rand.19	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in 3 = X); elpi z_report "rand.19" "3" ltac_term:(G)) | idtac "SSR	rand.19	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.19" "4" ltac_term:(G)) | idtac "SSR	rand.19	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.19" "5" ltac_term:(G)) | idtac "SSR	rand.19	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.19" "6" ltac_term:(G)) | idtac "SSR	rand.19	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.19" "7" ltac_term:(G)) | idtac "SSR	rand.19	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.19" "8" ltac_term:(G)) | idtac "SSR	rand.19	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.19" "9" ltac_term:(G)) | idtac "SSR	rand.19	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.19" "10" ltac_term:(G)) | idtac "SSR	rand.19	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 = X); elpi z_report "rand.19" "11" ltac_term:(G)) | idtac "SSR	rand.19	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = 1); elpi z_report "rand.19" "12" ltac_term:(G)) | idtac "SSR	rand.19	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (c, ((length (l ++ l)) + (g (length l))))) = 
(g (snd (((fst (b, a)) + (fst (1, b))), b))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g (snd (fst (b, a) + X, _))); elpi z_report "rand.20" "1" ltac_term:(G)) | idtac "SSR	rand.20	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (fst (b, a) + X, b)); elpi z_report "rand.20" "2" ltac_term:(G)) | idtac "SSR	rand.20	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (c, length (l ++ l) + g (length l)) = g (snd (fst (b, a) + fst (X, b), b))); elpi z_report "rand.20" "3" ltac_term:(G)) | idtac "SSR	rand.20	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (X, _)); elpi z_report "rand.20" "4" ltac_term:(G)) | idtac "SSR	rand.20	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (fst (b, _) + fst (X, _), _)); elpi z_report "rand.20" "5" ltac_term:(G)) | idtac "SSR	rand.20	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (fst (b, a) + fst (X, _), _)); elpi z_report "rand.20" "6" ltac_term:(G)) | idtac "SSR	rand.20	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst (b, a) + fst X); elpi z_report "rand.20" "7" ltac_term:(G)) | idtac "SSR	rand.20	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (X, b)); elpi z_report "rand.20" "8" ltac_term:(G)) | idtac "SSR	rand.20	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (b, a) + fst (X, _)); elpi z_report "rand.20" "9" ltac_term:(G)) | idtac "SSR	rand.20	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in fst (b, a) + fst (X, b)); elpi z_report "rand.20" "10" ltac_term:(G)) | idtac "SSR	rand.20	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (X, b)); elpi z_report "rand.20" "11" ltac_term:(G)) | idtac "SSR	rand.20	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.20" "12" ltac_term:(G)) | idtac "SSR	rand.20	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = (g 2) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.21" "1" ltac_term:(G)) | idtac "SSR	rand.21	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.21" "2" ltac_term:(G)) | idtac "SSR	rand.21	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in a = g (S X)); elpi z_report "rand.21" "3" ltac_term:(G)) | idtac "SSR	rand.21	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.21" "4" ltac_term:(G)) | idtac "SSR	rand.21	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.21" "5" ltac_term:(G)) | idtac "SSR	rand.21	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.21" "6" ltac_term:(G)) | idtac "SSR	rand.21	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.21" "7" ltac_term:(G)) | idtac "SSR	rand.21	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.21" "8" ltac_term:(G)) | idtac "SSR	rand.21	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a = g (S X)); elpi z_report "rand.21" "9" ltac_term:(G)) | idtac "SSR	rand.21	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in a = g (S X)); elpi z_report "rand.21" "10" ltac_term:(G)) | idtac "SSR	rand.21	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.21" "11" ltac_term:(G)) | idtac "SSR	rand.21	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in a = g X); elpi z_report "rand.21" "12" ltac_term:(G)) | idtac "SSR	rand.21	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = (snd (0, b)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0, _); elpi z_report "rand.22" "1" ltac_term:(G)) | idtac "SSR	rand.22	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((_, b) as X in length l = snd X); elpi z_report "rand.22" "2" ltac_term:(G)) | idtac "SSR	rand.22	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0, _); elpi z_report "rand.22" "3" ltac_term:(G)) | idtac "SSR	rand.22	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, _); elpi z_report "rand.22" "4" ltac_term:(G)) | idtac "SSR	rand.22	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0, b); elpi z_report "rand.22" "5" ltac_term:(G)) | idtac "SSR	rand.22	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, _) in X in snd X); elpi z_report "rand.22" "6" ltac_term:(G)) | idtac "SSR	rand.22	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0, b); elpi z_report "rand.22" "7" ltac_term:(G)) | idtac "SSR	rand.22	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, b) in X in length l = X); elpi z_report "rand.22" "8" ltac_term:(G)) | idtac "SSR	rand.22	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, b) as X in snd X); elpi z_report "rand.22" "9" ltac_term:(G)) | idtac "SSR	rand.22	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length _ = snd X); elpi z_report "rand.22" "10" ltac_term:(G)) | idtac "SSR	rand.22	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, _) in X in length l = X); elpi z_report "rand.22" "11" ltac_term:(G)) | idtac "SSR	rand.22	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((0, b) in X in length l = X); elpi z_report "rand.22" "12" ltac_term:(G)) | idtac "SSR	rand.22	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.23" "1" ltac_term:(G)) | idtac "SSR	rand.23	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = _); elpi z_report "rand.23" "2" ltac_term:(G)) | idtac "SSR	rand.23	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.23" "3" ltac_term:(G)) | idtac "SSR	rand.23	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = b); elpi z_report "rand.23" "4" ltac_term:(G)) | idtac "SSR	rand.23	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = _); elpi z_report "rand.23" "5" ltac_term:(G)) | idtac "SSR	rand.23	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.23" "6" ltac_term:(G)) | idtac "SSR	rand.23	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = _); elpi z_report "rand.23" "7" ltac_term:(G)) | idtac "SSR	rand.23	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.23" "8" ltac_term:(G)) | idtac "SSR	rand.23	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = b); elpi z_report "rand.23" "9" ltac_term:(G)) | idtac "SSR	rand.23	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.23" "10" ltac_term:(G)) | idtac "SSR	rand.23	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = _); elpi z_report "rand.23" "11" ltac_term:(G)) | idtac "SSR	rand.23	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.23" "12" ltac_term:(G)) | idtac "SSR	rand.23	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (b * (g ((g 2) + (fst (2, 2))))) = 
(snd ((g ((fst (0, 1)) + (0 * 1))), ((length (c :: l)) * 0))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ :: _); elpi z_report "rand.24" "1" ltac_term:(G)) | idtac "SSR	rand.24	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c :: l); elpi z_report "rand.24" "2" ltac_term:(G)) | idtac "SSR	rand.24	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in snd (g (fst (0, 1) + 0 * 1), X)); elpi z_report "rand.24" "3" ltac_term:(G)) | idtac "SSR	rand.24	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _); elpi z_report "rand.24" "4" ltac_term:(G)) | idtac "SSR	rand.24	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c :: l in X in (g (fst (0, 1) + 0 * 1), X)); elpi z_report "rand.24" "5" ltac_term:(G)) | idtac "SSR	rand.24	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c :: _ in X in (g (fst (0, 1) + 0 * 1), X)); elpi z_report "rand.24" "6" ltac_term:(G)) | idtac "SSR	rand.24	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c :: _ as X in length X); elpi z_report "rand.24" "7" ltac_term:(G)) | idtac "SSR	rand.24	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in b * g (g 2 + fst (2, 2)) = snd (g (fst (0, 1) + 0 * 1), X)); elpi z_report "rand.24" "8" ltac_term:(G)) | idtac "SSR	rand.24	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c :: _ as X in b * g (g 2 + fst (2, 2)) = snd (g (fst (0, 1) + 0 * 1), length X * _)); elpi z_report "rand.24" "9" ltac_term:(G)) | idtac "SSR	rand.24	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in b * g (g 2 + fst (2, 2)) = X); elpi z_report "rand.24" "10" ltac_term:(G)) | idtac "SSR	rand.24	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c :: l as X in length X * 0); elpi z_report "rand.24" "11" ltac_term:(G)) | idtac "SSR	rand.24	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in b * g (g 2 + fst (2, 2)) = snd (g (fst (0, 1) + 0 * 1), length X * 0)); elpi z_report "rand.24" "12" ltac_term:(G)) | idtac "SSR	rand.24	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (length ((a :: l) ++ (0 :: l)))) = (fst (2, (2 * c))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.25" "1" ltac_term:(G)) | idtac "SSR	rand.25	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in g (length ((a :: l) ++ 0 :: l)) = fst (2, X * c)); elpi z_report "rand.25" "2" ltac_term:(G)) | idtac "SSR	rand.25	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X * _); elpi z_report "rand.25" "3" ltac_term:(G)) | idtac "SSR	rand.25	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (length ((a :: l) ++ 0 :: l)) = fst (2, S X * _)); elpi z_report "rand.25" "4" ltac_term:(G)) | idtac "SSR	rand.25	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.25" "5" ltac_term:(G)) | idtac "SSR	rand.25	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X * c); elpi z_report "rand.25" "6" ltac_term:(G)) | idtac "SSR	rand.25	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.25" "7" ltac_term:(G)) | idtac "SSR	rand.25	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.25" "8" ltac_term:(G)) | idtac "SSR	rand.25	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (S X, 2 * c)); elpi z_report "rand.25" "9" ltac_term:(G)) | idtac "SSR	rand.25	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (X, 2 * c)); elpi z_report "rand.25" "10" ltac_term:(G)) | idtac "SSR	rand.25	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in fst (2, S X * c)); elpi z_report "rand.25" "11" ltac_term:(G)) | idtac "SSR	rand.25	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (length ((a :: l) ++ 0 :: l)) = fst (2, S X * _)); elpi z_report "rand.25" "12" ltac_term:(G)) | idtac "SSR	rand.25	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((snd (3, c)) * (length l)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in X = snd (3, c) * length l); elpi z_report "rand.26" "1" ltac_term:(G)) | idtac "SSR	rand.26	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.26" "2" ltac_term:(G)) | idtac "SSR	rand.26	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = snd (3, c) * length l); elpi z_report "rand.26" "3" ltac_term:(G)) | idtac "SSR	rand.26	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.26" "4" ltac_term:(G)) | idtac "SSR	rand.26	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.26" "5" ltac_term:(G)) | idtac "SSR	rand.26	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _ in X in snd (3, c) * X); elpi z_report "rand.26" "6" ltac_term:(G)) | idtac "SSR	rand.26	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l = snd (3, c) * X); elpi z_report "rand.26" "7" ltac_term:(G)) | idtac "SSR	rand.26	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in snd (3, _) * X); elpi z_report "rand.26" "8" ltac_term:(G)) | idtac "SSR	rand.26	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in X = snd (3, c) * length l); elpi z_report "rand.26" "9" ltac_term:(G)) | idtac "SSR	rand.26	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.26" "10" ltac_term:(G)) | idtac "SSR	rand.26	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.26" "11" ltac_term:(G)) | idtac "SSR	rand.26	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in X = snd (3, c) * _); elpi z_report "rand.26" "12" ltac_term:(G)) | idtac "SSR	rand.26	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length (((l ++ l) ++ l) ++ l)) = 
b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((X ++ l) ++ _) = _); elpi z_report "rand.27" "1" ltac_term:(G)) | idtac "SSR	rand.27	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ l); elpi z_report "rand.27" "2" ltac_term:(G)) | idtac "SSR	rand.27	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (X ++ l) ++ _); elpi z_report "rand.27" "3" ltac_term:(G)) | idtac "SSR	rand.27	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((X ++ l) ++ _)); elpi z_report "rand.27" "4" ltac_term:(G)) | idtac "SSR	rand.27	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in length ((X ++ _) ++ _)); elpi z_report "rand.27" "5" ltac_term:(G)) | idtac "SSR	rand.27	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ l in X in X ++ _); elpi z_report "rand.27" "6" ltac_term:(G)) | idtac "SSR	rand.27	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in length ((X ++ l) ++ l) = _); elpi z_report "rand.27" "7" ltac_term:(G)) | idtac "SSR	rand.27	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ _ in X in length X); elpi z_report "rand.27" "8" ltac_term:(G)) | idtac "SSR	rand.27	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in X ++ _); elpi z_report "rand.27" "9" ltac_term:(G)) | idtac "SSR	rand.27	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ _ in X in length X = _); elpi z_report "rand.27" "10" ltac_term:(G)) | idtac "SSR	rand.27	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in X ++ _); elpi z_report "rand.27" "11" ltac_term:(G)) | idtac "SSR	rand.27	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in X ++ _); elpi z_report "rand.27" "12" ltac_term:(G)) | idtac "SSR	rand.27	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((l ++ l) ++ (l ++ (l ++ l)))) = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.28" "1" ltac_term:(G)) | idtac "SSR	rand.28	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ l as X in length (X ++ l ++ l ++ l)); elpi z_report "rand.28" "2" ltac_term:(G)) | idtac "SSR	rand.28	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l as X in length ((_ ++ _) ++ l ++ X) = _); elpi z_report "rand.28" "3" ltac_term:(G)) | idtac "SSR	rand.28	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in length (X ++ _)); elpi z_report "rand.28" "4" ltac_term:(G)) | idtac "SSR	rand.28	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ l as X in l ++ X); elpi z_report "rand.28" "5" ltac_term:(G)) | idtac "SSR	rand.28	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in length (X ++ l ++ l ++ l)); elpi z_report "rand.28" "6" ltac_term:(G)) | idtac "SSR	rand.28	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X ++ l ++ l ++ l); elpi z_report "rand.28" "7" ltac_term:(G)) | idtac "SSR	rand.28	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in (_ ++ l) ++ X); elpi z_report "rand.28" "8" ltac_term:(G)) | idtac "SSR	rand.28	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in X ++ l ++ l ++ _); elpi z_report "rand.28" "9" ltac_term:(G)) | idtac "SSR	rand.28	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.28" "10" ltac_term:(G)) | idtac "SSR	rand.28	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in length ((l ++ l) ++ X) = _); elpi z_report "rand.28" "11" ltac_term:(G)) | idtac "SSR	rand.28	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.28" "12" ltac_term:(G)) | idtac "SSR	rand.28	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((g (b * 3)), (length (l ++ l)))) * 1) = 
(fst (0, (length ((l ++ l) ++ l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l as X in (g (_ * 3), length X)); elpi z_report "rand.29" "1" ltac_term:(G)) | idtac "SSR	rand.29	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.29" "2" ltac_term:(G)) | idtac "SSR	rand.29	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in (_, length X)); elpi z_report "rand.29" "3" ltac_term:(G)) | idtac "SSR	rand.29	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.29" "4" ltac_term:(G)) | idtac "SSR	rand.29	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ l as X in X ++ _); elpi z_report "rand.29" "5" ltac_term:(G)) | idtac "SSR	rand.29	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in length X); elpi z_report "rand.29" "6" ltac_term:(G)) | idtac "SSR	rand.29	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in fst (g (b * 3), length (l ++ l)) * 1 = X); elpi z_report "rand.29" "7" ltac_term:(G)) | idtac "SSR	rand.29	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in length (X ++ _)); elpi z_report "rand.29" "8" ltac_term:(G)) | idtac "SSR	rand.29	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in fst X * _ = fst (0, length ((l ++ l) ++ l))); elpi z_report "rand.29" "9" ltac_term:(G)) | idtac "SSR	rand.29	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ _ in X in fst X * 1 = fst (0, length ((l ++ l) ++ l))); elpi z_report "rand.29" "10" ltac_term:(G)) | idtac "SSR	rand.29	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (g (b * 3), length X)); elpi z_report "rand.29" "11" ltac_term:(G)) | idtac "SSR	rand.29	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in fst (g (b * 3), length X) * 1); elpi z_report "rand.29" "12" ltac_term:(G)) | idtac "SSR	rand.29	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((fst ((g 0), 3)) * 2) + ((length (b :: l)) * (f (a * b) (0 + a)))) = 
(length (((fst (a, 1)) :: (l ++ l)) ++ l)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.30" "1" ltac_term:(G)) | idtac "SSR	rand.30	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ _ in X in X ++ l); elpi z_report "rand.30" "2" ltac_term:(G)) | idtac "SSR	rand.30	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in length ((fst (a, 1) :: X) ++ _)); elpi z_report "rand.30" "3" ltac_term:(G)) | idtac "SSR	rand.30	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.30" "4" ltac_term:(G)) | idtac "SSR	rand.30	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (a, 1) :: X); elpi z_report "rand.30" "5" ltac_term:(G)) | idtac "SSR	rand.30	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.30" "6" ltac_term:(G)) | idtac "SSR	rand.30	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in X ++ _); elpi z_report "rand.30" "7" ltac_term:(G)) | idtac "SSR	rand.30	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ l); elpi z_report "rand.30" "8" ltac_term:(G)) | idtac "SSR	rand.30	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ _ as X in fst (g 0, 3) * 2 + length (b :: l) * f (a * b) (0 + a) = length ((fst (a, 1) :: X) ++ l)); elpi z_report "rand.30" "9" ltac_term:(G)) | idtac "SSR	rand.30	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ _ as X in fst _ :: X); elpi z_report "rand.30" "10" ltac_term:(G)) | idtac "SSR	rand.30	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in length X); elpi z_report "rand.30" "11" ltac_term:(G)) | idtac "SSR	rand.30	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in length (X ++ _)); elpi z_report "rand.30" "12" ltac_term:(G)) | idtac "SSR	rand.30	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (0, (fst (((c + 1) * (c * a)), (fst (0, (fst (a, c)))))))) = 
((f (fst ((g 1), (g 2))) (g 1)) + (a * (g (2 + b)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.31" "1" ltac_term:(G)) | idtac "SSR	rand.31	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst ((c + X) * (c * a), fst (0, fst (a, c)))); elpi z_report "rand.31" "2" ltac_term:(G)) | idtac "SSR	rand.31	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (fst (X, g 2)) (g 1)); elpi z_report "rand.31" "3" ltac_term:(G)) | idtac "SSR	rand.31	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.31" "4" ltac_term:(G)) | idtac "SSR	rand.31	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.31" "5" ltac_term:(G)) | idtac "SSR	rand.31	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g X); elpi z_report "rand.31" "6" ltac_term:(G)) | idtac "SSR	rand.31	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (fst (X, g 2)) (g 1)); elpi z_report "rand.31" "7" ltac_term:(G)) | idtac "SSR	rand.31	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.31" "8" ltac_term:(G)) | idtac "SSR	rand.31	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (fst (g 1, g 2)) (g X) + _ * g (2 + b)); elpi z_report "rand.31" "9" ltac_term:(G)) | idtac "SSR	rand.31	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g 1, g (S X))); elpi z_report "rand.31" "10" ltac_term:(G)) | idtac "SSR	rand.31	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in f (fst (g 1, g 2)) (g X)); elpi z_report "rand.31" "11" ltac_term:(G)) | idtac "SSR	rand.31	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _); elpi z_report "rand.31" "12" ltac_term:(G)) | idtac "SSR	rand.31	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = a .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.32" "1" ltac_term:(G)) | idtac "SSR	rand.32	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = a); elpi z_report "rand.32" "2" ltac_term:(G)) | idtac "SSR	rand.32	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = a); elpi z_report "rand.32" "3" ltac_term:(G)) | idtac "SSR	rand.32	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.32" "4" ltac_term:(G)) | idtac "SSR	rand.32	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ = a); elpi z_report "rand.32" "5" ltac_term:(G)) | idtac "SSR	rand.32	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.32" "6" ltac_term:(G)) | idtac "SSR	rand.32	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = a); elpi z_report "rand.32" "7" ltac_term:(G)) | idtac "SSR	rand.32	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(c = _); elpi z_report "rand.32" "8" ltac_term:(G)) | idtac "SSR	rand.32	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = a); elpi z_report "rand.32" "9" ltac_term:(G)) | idtac "SSR	rand.32	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = a); elpi z_report "rand.32" "10" ltac_term:(G)) | idtac "SSR	rand.32	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c = _); elpi z_report "rand.32" "11" ltac_term:(G)) | idtac "SSR	rand.32	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.32" "12" ltac_term:(G)) | idtac "SSR	rand.32	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
(0 + ((length l) + (0 * (f c 1)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = _ + (length _ + 0 * X)); elpi z_report "rand.33" "1" ltac_term:(G)) | idtac "SSR	rand.33	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in length l + 0 * f c X); elpi z_report "rand.33" "2" ltac_term:(G)) | idtac "SSR	rand.33	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * f c X); elpi z_report "rand.33" "3" ltac_term:(G)) | idtac "SSR	rand.33	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in length l + _ * f _ X); elpi z_report "rand.33" "4" ltac_term:(G)) | idtac "SSR	rand.33	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f c X); elpi z_report "rand.33" "5" ltac_term:(G)) | idtac "SSR	rand.33	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.33" "6" ltac_term:(G)) | idtac "SSR	rand.33	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.33" "7" ltac_term:(G)) | idtac "SSR	rand.33	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + (_ + X)); elpi z_report "rand.33" "8" ltac_term:(G)) | idtac "SSR	rand.33	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + (length _ + 0 * f _ X)); elpi z_report "rand.33" "9" ltac_term:(G)) | idtac "SSR	rand.33	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l + _ * f _ X); elpi z_report "rand.33" "10" ltac_term:(G)) | idtac "SSR	rand.33	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ X); elpi z_report "rand.33" "11" ltac_term:(G)) | idtac "SSR	rand.33	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = 0 + (_ + X)); elpi z_report "rand.33" "12" ltac_term:(G)) | idtac "SSR	rand.33	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g 3) = 0 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.34" "1" ltac_term:(G)) | idtac "SSR	rand.34	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.34" "2" ltac_term:(G)) | idtac "SSR	rand.34	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S (S X))); elpi z_report "rand.34" "3" ltac_term:(G)) | idtac "SSR	rand.34	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.34" "4" ltac_term:(G)) | idtac "SSR	rand.34	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.34" "5" ltac_term:(G)) | idtac "SSR	rand.34	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S (S X)) = 0); elpi z_report "rand.34" "6" ltac_term:(G)) | idtac "SSR	rand.34	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.34" "7" ltac_term:(G)) | idtac "SSR	rand.34	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S (S X)); elpi z_report "rand.34" "8" ltac_term:(G)) | idtac "SSR	rand.34	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S (S X))); elpi z_report "rand.34" "9" ltac_term:(G)) | idtac "SSR	rand.34	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.34" "10" ltac_term:(G)) | idtac "SSR	rand.34	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.34" "11" ltac_term:(G)) | idtac "SSR	rand.34	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (S (S X)) = 0); elpi z_report "rand.34" "12" ltac_term:(G)) | idtac "SSR	rand.34	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((fst (b, (g (snd (b, a))))), (((snd (b, a)) + a) * (f (length l) (fst (0, b)))))) 
= ((fst (b, (f (fst (c, b)) (fst (2, 0))))) * (fst (3, (f c (length l))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in fst (b, f (fst (c, b)) (fst (2, 0))) * fst (3, f _ X)); elpi z_report "rand.35" "1" ltac_term:(G)) | idtac "SSR	rand.35	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.35" "2" ltac_term:(G)) | idtac "SSR	rand.35	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.35" "3" ltac_term:(G)) | idtac "SSR	rand.35	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in fst (b, f (fst (c, b)) (fst (2, 0))) * fst X); elpi z_report "rand.35" "4" ltac_term:(G)) | idtac "SSR	rand.35	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in fst (fst (b, g (snd (b, a))), (snd (b, a) + a) * f X (fst (0, b))) = fst (b, f (fst (c, b)) (fst (2, 0))) * fst (3, f c (length l))); elpi z_report "rand.35" "5" ltac_term:(G)) | idtac "SSR	rand.35	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in fst (fst (b, g (snd (b, a))), (snd (b, a) + a) * f (length l) (fst (0, b))) = fst (b, f (fst (c, b)) (fst (2, 0))) * fst (3, f c X)); elpi z_report "rand.35" "6" ltac_term:(G)) | idtac "SSR	rand.35	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l in X in (fst (b, g (snd (b, a))), (snd (b, a) + _) * X)); elpi z_report "rand.35" "7" ltac_term:(G)) | idtac "SSR	rand.35	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.35" "8" ltac_term:(G)) | idtac "SSR	rand.35	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.35" "9" ltac_term:(G)) | idtac "SSR	rand.35	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (snd (b, a) + _) * f X (fst (0, b))); elpi z_report "rand.35" "10" ltac_term:(G)) | idtac "SSR	rand.35	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.35" "11" ltac_term:(G)) | idtac "SSR	rand.35	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l in X in fst (3, X)); elpi z_report "rand.35" "12" ltac_term:(G)) | idtac "SSR	rand.35	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((g ((b + 0) + (length l))) * (g (f (c + 0) (length l)))) = 
(snd ((length (l ++ (a :: l))), c)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (length (_ ++ X), _)); elpi z_report "rand.36" "1" ltac_term:(G)) | idtac "SSR	rand.36	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in snd (length X, _)); elpi z_report "rand.36" "2" ltac_term:(G)) | idtac "SSR	rand.36	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _ as X in length (_ ++ X)); elpi z_report "rand.36" "3" ltac_term:(G)) | idtac "SSR	rand.36	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ as X in g (b + 0 + length l) * g (f (c + 0) (length l)) = snd (length (l ++ X), _)); elpi z_report "rand.36" "4" ltac_term:(G)) | idtac "SSR	rand.36	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _); elpi z_report "rand.36" "5" ltac_term:(G)) | idtac "SSR	rand.36	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (_ ++ X)); elpi z_report "rand.36" "6" ltac_term:(G)) | idtac "SSR	rand.36	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _ as X in length (_ ++ X)); elpi z_report "rand.36" "7" ltac_term:(G)) | idtac "SSR	rand.36	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _ as X in g (b + 0 + length l) * g (f (c + 0) (length l)) = snd (length (l ++ X), _)); elpi z_report "rand.36" "8" ltac_term:(G)) | idtac "SSR	rand.36	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (length (_ ++ X), c)); elpi z_report "rand.36" "9" ltac_term:(G)) | idtac "SSR	rand.36	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _); elpi z_report "rand.36" "10" ltac_term:(G)) | idtac "SSR	rand.36	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: l in X in (length X, c)); elpi z_report "rand.36" "11" ltac_term:(G)) | idtac "SSR	rand.36	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: l); elpi z_report "rand.36" "12" ltac_term:(G)) | idtac "SSR	rand.36	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = S X); elpi z_report "rand.37" "1" ltac_term:(G)) | idtac "SSR	rand.37	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.37" "2" ltac_term:(G)) | idtac "SSR	rand.37	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in b = S X); elpi z_report "rand.37" "3" ltac_term:(G)) | idtac "SSR	rand.37	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ = S X); elpi z_report "rand.37" "4" ltac_term:(G)) | idtac "SSR	rand.37	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.37" "5" ltac_term:(G)) | idtac "SSR	rand.37	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X); elpi z_report "rand.37" "6" ltac_term:(G)) | idtac "SSR	rand.37	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.37" "7" ltac_term:(G)) | idtac "SSR	rand.37	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.37" "8" ltac_term:(G)) | idtac "SSR	rand.37	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in b = S X); elpi z_report "rand.37" "9" ltac_term:(G)) | idtac "SSR	rand.37	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.37" "10" ltac_term:(G)) | idtac "SSR	rand.37	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in _ = X); elpi z_report "rand.37" "11" ltac_term:(G)) | idtac "SSR	rand.37	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X); elpi z_report "rand.37" "12" ltac_term:(G)) | idtac "SSR	rand.37	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((length (c :: l)), (snd ((3 * 3), (length l))))) + (fst (c, ((length l) + c)))) 
= (g (snd ((snd ((f 3 0), (length l))), (length (l ++ l))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.38" "1" ltac_term:(G)) | idtac "SSR	rand.38	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (snd (f 3 _, _), length X)); elpi z_report "rand.38" "2" ltac_term:(G)) | idtac "SSR	rand.38	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in g (snd X)); elpi z_report "rand.38" "3" ltac_term:(G)) | idtac "SSR	rand.38	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.38" "4" ltac_term:(G)) | idtac "SSR	rand.38	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in fst (length (c :: l), snd (3 * 3, length l)) + fst (c, length l + c) = g (snd (snd (f 3 0, length l), length X))); elpi z_report "rand.38" "5" ltac_term:(G)) | idtac "SSR	rand.38	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X); elpi z_report "rand.38" "6" ltac_term:(G)) | idtac "SSR	rand.38	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in snd (snd (f 3 0, length l), X)); elpi z_report "rand.38" "7" ltac_term:(G)) | idtac "SSR	rand.38	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in fst (length (c :: l), snd (3 * 3, length l)) + fst (c, length l + c) = g (snd (snd (f 3 0, length l), length X))); elpi z_report "rand.38" "8" ltac_term:(G)) | idtac "SSR	rand.38	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l as X in snd (snd (f 3 0, length l), length X)); elpi z_report "rand.38" "9" ltac_term:(G)) | idtac "SSR	rand.38	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (length (c :: l), snd (3 * 3, length l)) + fst (c, length l + c) = g (snd (snd (f 3 0, length l), length X))); elpi z_report "rand.38" "10" ltac_term:(G)) | idtac "SSR	rand.38	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in length X); elpi z_report "rand.38" "11" ltac_term:(G)) | idtac "SSR	rand.38	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ _ as X in snd (snd (f 3 _, length l), length X)); elpi z_report "rand.38" "12" ltac_term:(G)) | idtac "SSR	rand.38	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X); elpi z_report "rand.39" "1" ltac_term:(G)) | idtac "SSR	rand.39	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = S X); elpi z_report "rand.39" "2" ltac_term:(G)) | idtac "SSR	rand.39	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.39" "3" ltac_term:(G)) | idtac "SSR	rand.39	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = S X); elpi z_report "rand.39" "4" ltac_term:(G)) | idtac "SSR	rand.39	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in c = X); elpi z_report "rand.39" "5" ltac_term:(G)) | idtac "SSR	rand.39	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c = S X); elpi z_report "rand.39" "6" ltac_term:(G)) | idtac "SSR	rand.39	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X); elpi z_report "rand.39" "7" ltac_term:(G)) | idtac "SSR	rand.39	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.39" "8" ltac_term:(G)) | idtac "SSR	rand.39	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.39" "9" ltac_term:(G)) | idtac "SSR	rand.39	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X); elpi z_report "rand.39" "10" ltac_term:(G)) | idtac "SSR	rand.39	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in S X); elpi z_report "rand.39" "11" ltac_term:(G)) | idtac "SSR	rand.39	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _); elpi z_report "rand.39" "12" ltac_term:(G)) | idtac "SSR	rand.39	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = (g a) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in 1 = X); elpi z_report "rand.40" "1" ltac_term:(G)) | idtac "SSR	rand.40	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in _ = X); elpi z_report "rand.40" "2" ltac_term:(G)) | idtac "SSR	rand.40	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.40" "3" ltac_term:(G)) | idtac "SSR	rand.40	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a as X in 1 = X); elpi z_report "rand.40" "4" ltac_term:(G)) | idtac "SSR	rand.40	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in 1 = X); elpi z_report "rand.40" "5" ltac_term:(G)) | idtac "SSR	rand.40	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g a as X in 1 = X); elpi z_report "rand.40" "6" ltac_term:(G)) | idtac "SSR	rand.40	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in 1 = X); elpi z_report "rand.40" "7" ltac_term:(G)) | idtac "SSR	rand.40	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in 1 = X); elpi z_report "rand.40" "8" ltac_term:(G)) | idtac "SSR	rand.40	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a as X in 1 = X); elpi z_report "rand.40" "9" ltac_term:(G)) | idtac "SSR	rand.40	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a in X in 1 = X); elpi z_report "rand.40" "10" ltac_term:(G)) | idtac "SSR	rand.40	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a in X in S _ = X); elpi z_report "rand.40" "11" ltac_term:(G)) | idtac "SSR	rand.40	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.40" "12" ltac_term:(G)) | idtac "SSR	rand.40	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (((g a) + 3), (length l))) = 
(fst ((f 1 (length l)), (snd (((f b 0) + (b * 3)), b)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.41" "1" ltac_term:(G)) | idtac "SSR	rand.41	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst X); elpi z_report "rand.41" "2" ltac_term:(G)) | idtac "SSR	rand.41	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g a + X); elpi z_report "rand.41" "3" ltac_term:(G)) | idtac "SSR	rand.41	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.41" "4" ltac_term:(G)) | idtac "SSR	rand.41	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (g a + S X, length l)); elpi z_report "rand.41" "5" ltac_term:(G)) | idtac "SSR	rand.41	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (g a + S (S X), _)); elpi z_report "rand.41" "6" ltac_term:(G)) | idtac "SSR	rand.41	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (g a + 3, length l) = fst (f 1 (length l), snd (f b 0 + b * S (S X), b))); elpi z_report "rand.41" "7" ltac_term:(G)) | idtac "SSR	rand.41	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (f X (length l), snd (f b 0 + b * 3, b))); elpi z_report "rand.41" "8" ltac_term:(G)) | idtac "SSR	rand.41	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.41" "9" ltac_term:(G)) | idtac "SSR	rand.41	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.41" "10" ltac_term:(G)) | idtac "SSR	rand.41	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.41" "11" ltac_term:(G)) | idtac "SSR	rand.41	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.41" "12" ltac_term:(G)) | idtac "SSR	rand.41	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((f (f 2 c) (snd (b, c))) * (fst ((1 * 2), (g 1)))) + (((1 * a) * (fst (0, 3))) * (length (c :: l)))) 
= (g (g ((snd (1, 1)) + b))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (f 2 _) (snd (b, _)) * fst (X * S (S _), g 1)); elpi z_report "rand.42" "1" ltac_term:(G)) | idtac "SSR	rand.42	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.42" "2" ltac_term:(G)) | idtac "SSR	rand.42	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + 1 * a * fst (0, 3) * length (c :: l) = g (g (snd (1, 1) + b))); elpi z_report "rand.42" "3" ltac_term:(G)) | idtac "SSR	rand.42	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in f (f 2 c) (snd (b, c)) * fst (X * 2, g 1) + 1 * a * fst (0, 3) * length (c :: l)); elpi z_report "rand.42" "4" ltac_term:(G)) | idtac "SSR	rand.42	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.42" "5" ltac_term:(G)) | idtac "SSR	rand.42	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in f (f 2 c) (snd (b, c)) * fst (_ * S X, g 1)); elpi z_report "rand.42" "6" ltac_term:(G)) | idtac "SSR	rand.42	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (f (S X) c) (snd (b, c)) * fst (1 * 2, g 1) + 1 * a * fst (0, 3) * length (c :: l)); elpi z_report "rand.42" "7" ltac_term:(G)) | idtac "SSR	rand.42	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in 1 * a * fst (_, S (S X))); elpi z_report "rand.42" "8" ltac_term:(G)) | idtac "SSR	rand.42	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in S X); elpi z_report "rand.42" "9" ltac_term:(G)) | idtac "SSR	rand.42	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f (S X) _) (snd (_, _)) * fst (1 * 2, g 1) + 1 * a * fst (_, 3) * length (c :: _) = g (g (snd (1, 1) + b))); elpi z_report "rand.42" "10" ltac_term:(G)) | idtac "SSR	rand.42	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in f (f 2 c) (snd (b, c)) * fst (1 * 2, g 1) + 1 * a * fst (0, 3) * length (c :: l) = g (g (snd (X, 1) + b))); elpi z_report "rand.42" "11" ltac_term:(G)) | idtac "SSR	rand.42	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (g (snd (1, X) + _))); elpi z_report "rand.42" "12" ltac_term:(G)) | idtac "SSR	rand.42	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (c, 1)) = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (c, X) = 2); elpi z_report "rand.43" "1" ltac_term:(G)) | idtac "SSR	rand.43	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, X)); elpi z_report "rand.43" "2" ltac_term:(G)) | idtac "SSR	rand.43	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in snd (c, 1) = S X); elpi z_report "rand.43" "3" ltac_term:(G)) | idtac "SSR	rand.43	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, X)); elpi z_report "rand.43" "4" ltac_term:(G)) | idtac "SSR	rand.43	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (c, 1) = S X); elpi z_report "rand.43" "5" ltac_term:(G)) | idtac "SSR	rand.43	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (c, X) = 2); elpi z_report "rand.43" "6" ltac_term:(G)) | idtac "SSR	rand.43	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (c, 1) = S X); elpi z_report "rand.43" "7" ltac_term:(G)) | idtac "SSR	rand.43	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.43" "8" ltac_term:(G)) | idtac "SSR	rand.43	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.43" "9" ltac_term:(G)) | idtac "SSR	rand.43	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, X)); elpi z_report "rand.43" "10" ltac_term:(G)) | idtac "SSR	rand.43	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.43" "11" ltac_term:(G)) | idtac "SSR	rand.43	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in (_, X)); elpi z_report "rand.43" "12" ltac_term:(G)) | idtac "SSR	rand.43	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((g b) + (length (c :: l))), (((2 * c) * a) + (g (length l))))) = 
(fst (b, (a + (b + (f b 1))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + (_ + f _ X)); elpi z_report "rand.44" "1" ltac_term:(G)) | idtac "SSR	rand.44	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g b + length (c :: l), 2 * c * a + g (length l)) = fst (b, _ + (_ + f _ X))); elpi z_report "rand.44" "2" ltac_term:(G)) | idtac "SSR	rand.44	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in fst (_, _ + (b + f _ X))); elpi z_report "rand.44" "3" ltac_term:(G)) | idtac "SSR	rand.44	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X * _ * a + g (length l)); elpi z_report "rand.44" "4" ltac_term:(G)) | idtac "SSR	rand.44	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.44" "5" ltac_term:(G)) | idtac "SSR	rand.44	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X * a); elpi z_report "rand.44" "6" ltac_term:(G)) | idtac "SSR	rand.44	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, a + (_ + f b X))); elpi z_report "rand.44" "7" ltac_term:(G)) | idtac "SSR	rand.44	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (_, _ + (_ + f b X))); elpi z_report "rand.44" "8" ltac_term:(G)) | idtac "SSR	rand.44	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.44" "9" ltac_term:(G)) | idtac "SSR	rand.44	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.44" "10" ltac_term:(G)) | idtac "SSR	rand.44	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.44" "11" ltac_term:(G)) | idtac "SSR	rand.44	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X * c); elpi z_report "rand.44" "12" ltac_term:(G)) | idtac "SSR	rand.44	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g (length l)) = (0 + 3) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in g (length l) = _ + S (S X)); elpi z_report "rand.45" "1" ltac_term:(G)) | idtac "SSR	rand.45	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in g (length l) = X); elpi z_report "rand.45" "2" ltac_term:(G)) | idtac "SSR	rand.45	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.45" "3" ltac_term:(G)) | idtac "SSR	rand.45	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.45" "4" ltac_term:(G)) | idtac "SSR	rand.45	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.45" "5" ltac_term:(G)) | idtac "SSR	rand.45	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.45" "6" ltac_term:(G)) | idtac "SSR	rand.45	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.45" "7" ltac_term:(G)) | idtac "SSR	rand.45	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + S (S X)); elpi z_report "rand.45" "8" ltac_term:(G)) | idtac "SSR	rand.45	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.45" "9" ltac_term:(G)) | idtac "SSR	rand.45	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S (S X)); elpi z_report "rand.45" "10" ltac_term:(G)) | idtac "SSR	rand.45	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 0 + S X); elpi z_report "rand.45" "11" ltac_term:(G)) | idtac "SSR	rand.45	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in g (length l) = 0 + X); elpi z_report "rand.45" "12" ltac_term:(G)) | idtac "SSR	rand.45	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
((f (length (1 :: l)) (f c c)) * (length ((1 :: l) ++ (l ++ l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ l); elpi z_report "rand.46" "1" ltac_term:(G)) | idtac "SSR	rand.46	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in _ = X); elpi z_report "rand.46" "2" ltac_term:(G)) | idtac "SSR	rand.46	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in length X); elpi z_report "rand.46" "3" ltac_term:(G)) | idtac "SSR	rand.46	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in (S _ :: l) ++ X); elpi z_report "rand.46" "4" ltac_term:(G)) | idtac "SSR	rand.46	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.46" "5" ltac_term:(G)) | idtac "SSR	rand.46	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in length X); elpi z_report "rand.46" "6" ltac_term:(G)) | idtac "SSR	rand.46	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in a = f (length (1 :: l)) (f c c) * length ((1 :: l) ++ X)); elpi z_report "rand.46" "7" ltac_term:(G)) | idtac "SSR	rand.46	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.46" "8" ltac_term:(G)) | idtac "SSR	rand.46	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (1 :: l) ++ X); elpi z_report "rand.46" "9" ltac_term:(G)) | idtac "SSR	rand.46	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (length (1 :: l)) (f c c) * length ((1 :: _) ++ X)); elpi z_report "rand.46" "10" ltac_term:(G)) | idtac "SSR	rand.46	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.46" "11" ltac_term:(G)) | idtac "SSR	rand.46	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in length X); elpi z_report "rand.46" "12" ltac_term:(G)) | idtac "SSR	rand.46	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = c .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = c); elpi z_report "rand.47" "1" ltac_term:(G)) | idtac "SSR	rand.47	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = c); elpi z_report "rand.47" "2" ltac_term:(G)) | idtac "SSR	rand.47	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.47" "3" ltac_term:(G)) | idtac "SSR	rand.47	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = c); elpi z_report "rand.47" "4" ltac_term:(G)) | idtac "SSR	rand.47	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = c); elpi z_report "rand.47" "5" ltac_term:(G)) | idtac "SSR	rand.47	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = c); elpi z_report "rand.47" "6" ltac_term:(G)) | idtac "SSR	rand.47	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ = _); elpi z_report "rand.47" "7" ltac_term:(G)) | idtac "SSR	rand.47	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = c); elpi z_report "rand.47" "8" ltac_term:(G)) | idtac "SSR	rand.47	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = _); elpi z_report "rand.47" "9" ltac_term:(G)) | idtac "SSR	rand.47	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a = c); elpi z_report "rand.47" "10" ltac_term:(G)) | idtac "SSR	rand.47	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = c); elpi z_report "rand.47" "11" ltac_term:(G)) | idtac "SSR	rand.47	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = c); elpi z_report "rand.47" "12" ltac_term:(G)) | idtac "SSR	rand.47	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 1 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X = 1); elpi z_report "rand.48" "1" ltac_term:(G)) | idtac "SSR	rand.48	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in X = 1); elpi z_report "rand.48" "2" ltac_term:(G)) | idtac "SSR	rand.48	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 1 = X); elpi z_report "rand.48" "3" ltac_term:(G)) | idtac "SSR	rand.48	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in _ = X); elpi z_report "rand.48" "4" ltac_term:(G)) | idtac "SSR	rand.48	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in 1 = X); elpi z_report "rand.48" "5" ltac_term:(G)) | idtac "SSR	rand.48	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in 1 = X); elpi z_report "rand.48" "6" ltac_term:(G)) | idtac "SSR	rand.48	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 = X); elpi z_report "rand.48" "7" ltac_term:(G)) | idtac "SSR	rand.48	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in 1 = X); elpi z_report "rand.48" "8" ltac_term:(G)) | idtac "SSR	rand.48	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "rand.48" "9" ltac_term:(G)) | idtac "SSR	rand.48	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.48" "10" ltac_term:(G)) | idtac "SSR	rand.48	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.48" "11" ltac_term:(G)) | idtac "SSR	rand.48	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.48" "12" ltac_term:(G)) | idtac "SSR	rand.48	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (l ++ ((l ++ l) ++ (b :: l)))) = (f (length ((a :: l) ++ l)) 2) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.49" "1" ltac_term:(G)) | idtac "SSR	rand.49	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in length (l ++ (l ++ l) ++ b :: l) = f (length ((a :: l) ++ l)) (S X)); elpi z_report "rand.49" "2" ltac_term:(G)) | idtac "SSR	rand.49	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.49" "3" ltac_term:(G)) | idtac "SSR	rand.49	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (length ((a :: l) ++ l)) X); elpi z_report "rand.49" "4" ltac_term:(G)) | idtac "SSR	rand.49	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (length ((a :: l) ++ l)) (S X)); elpi z_report "rand.49" "5" ltac_term:(G)) | idtac "SSR	rand.49	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in length (_ ++ (l ++ l) ++ b :: l) = f (length ((a :: l) ++ l)) (S X)); elpi z_report "rand.49" "6" ltac_term:(G)) | idtac "SSR	rand.49	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in length (l ++ (l ++ l) ++ b :: l) = f (length ((a :: l) ++ l)) (S X)); elpi z_report "rand.49" "7" ltac_term:(G)) | idtac "SSR	rand.49	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (l ++ (l ++ l) ++ b :: l) = f (length ((a :: l) ++ l)) (S X)); elpi z_report "rand.49" "8" ltac_term:(G)) | idtac "SSR	rand.49	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.49" "9" ltac_term:(G)) | idtac "SSR	rand.49	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.49" "10" ltac_term:(G)) | idtac "SSR	rand.49	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.49" "11" ltac_term:(G)) | idtac "SSR	rand.49	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _); elpi z_report "rand.49" "12" ltac_term:(G)) | idtac "SSR	rand.49	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g (fst (0, (a + (0 * 2))))) = 
(fst ((fst ((snd ((0 + 3), (snd (3, 0)))), (fst ((fst (a, a)), (g b))))), ((snd (3, (fst (0, c)))) * ((length l) * 3)))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.50" "1" ltac_term:(G)) | idtac "SSR	rand.50	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g X); elpi z_report "rand.50" "2" ltac_term:(G)) | idtac "SSR	rand.50	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (0, _ + _ * S X)); elpi z_report "rand.50" "3" ltac_term:(G)) | idtac "SSR	rand.50	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (fst (snd (0 + S (S X), snd (3, _)), fst (fst (a, a), g b)), snd (3, fst (0, c)) * (length l * 3))); elpi z_report "rand.50" "4" ltac_term:(G)) | idtac "SSR	rand.50	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (snd (_ + 3, snd (S (S X), _)), fst (fst (a, a), g b))); elpi z_report "rand.50" "5" ltac_term:(G)) | idtac "SSR	rand.50	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in snd (S (S X), fst (0, c))); elpi z_report "rand.50" "6" ltac_term:(G)) | idtac "SSR	rand.50	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.50" "7" ltac_term:(G)) | idtac "SSR	rand.50	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ + S (S X)); elpi z_report "rand.50" "8" ltac_term:(G)) | idtac "SSR	rand.50	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in fst (fst (snd (0 + 3, snd (3, 0)), fst (fst (a, a), g b)), snd (S (S X), fst (0, c)) * (length l * 3))); elpi z_report "rand.50" "9" ltac_term:(G)) | idtac "SSR	rand.50	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (fst (snd (X, snd (3, 0)), fst (fst (a, a), g b)), snd (3, fst (0, c)) * (length l * 3))); elpi z_report "rand.50" "10" ltac_term:(G)) | idtac "SSR	rand.50	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (0 + X, snd (3, 0))); elpi z_report "rand.50" "11" ltac_term:(G)) | idtac "SSR	rand.50	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (fst (snd (0 + 3, snd (3, 0)), fst (fst (a, a), g b)), snd (3, fst (0, c)) * (length l * S (S X)))); elpi z_report "rand.50" "12" ltac_term:(G)) | idtac "SSR	rand.50	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((snd (((a * 1) + (g 2)), (snd ((g c), (f 1 0))))) * 0) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.51" "1" ltac_term:(G)) | idtac "SSR	rand.51	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in _ = snd (a * 1 + g 2, snd X) * _); elpi z_report "rand.51" "2" ltac_term:(G)) | idtac "SSR	rand.51	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in snd (X, snd (g c, f 1 0)) * 0); elpi z_report "rand.51" "3" ltac_term:(G)) | idtac "SSR	rand.51	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = snd (a * 1 + g 2, snd (g c, f 1 0)) * 0); elpi z_report "rand.51" "4" ltac_term:(G)) | idtac "SSR	rand.51	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (X, snd (g c, f 1 0))); elpi z_report "rand.51" "5" ltac_term:(G)) | idtac "SSR	rand.51	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S _ = snd (a * _ + g 2, snd (g c, f X 0)) * 0); elpi z_report "rand.51" "6" ltac_term:(G)) | idtac "SSR	rand.51	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X = snd (a * 1 + g 2, snd (g c, f 1 0)) * 0); elpi z_report "rand.51" "7" ltac_term:(G)) | idtac "SSR	rand.51	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in a * 1 + g (S X)); elpi z_report "rand.51" "8" ltac_term:(G)) | idtac "SSR	rand.51	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (g _, X)); elpi z_report "rand.51" "9" ltac_term:(G)) | idtac "SSR	rand.51	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = snd (a * 1 + g 2, snd (g c, f 1 0)) * 0); elpi z_report "rand.51" "10" ltac_term:(G)) | idtac "SSR	rand.51	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in (g c, f X 0)); elpi z_report "rand.51" "11" ltac_term:(G)) | idtac "SSR	rand.51	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in a * 1 + X); elpi z_report "rand.51" "12" ltac_term:(G)) | idtac "SSR	rand.51	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 
(length ((f (a * b) (3 * 0)) :: ((0 + a) :: (2 :: l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X :: l); elpi z_report "rand.52" "1" ltac_term:(G)) | idtac "SSR	rand.52	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in f _ (S (S X) * 0)); elpi z_report "rand.52" "2" ltac_term:(G)) | idtac "SSR	rand.52	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f (a * b) (X * _) :: 0 + a :: 2 :: l); elpi z_report "rand.52" "3" ltac_term:(G)) | idtac "SSR	rand.52	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 3 = length (f (a * b) (3 * 0) :: X)); elpi z_report "rand.52" "4" ltac_term:(G)) | idtac "SSR	rand.52	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in S X); elpi z_report "rand.52" "5" ltac_term:(G)) | idtac "SSR	rand.52	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (a * b) (S (S X) * _)); elpi z_report "rand.52" "6" ltac_term:(G)) | idtac "SSR	rand.52	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in S (S X)); elpi z_report "rand.52" "7" ltac_term:(G)) | idtac "SSR	rand.52	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.52" "8" ltac_term:(G)) | idtac "SSR	rand.52	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.52" "9" ltac_term:(G)) | idtac "SSR	rand.52	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (a * b) (S (S X) * 0) :: 0 + a :: 2 :: l); elpi z_report "rand.52" "10" ltac_term:(G)) | idtac "SSR	rand.52	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X) = length (f (a * b) (3 * 0) :: 0 + a :: 2 :: l)); elpi z_report "rand.52" "11" ltac_term:(G)) | idtac "SSR	rand.52	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = length (f (_ * b) (3 * 0) :: 0 + a :: 2 :: l)); elpi z_report "rand.52" "12" ltac_term:(G)) | idtac "SSR	rand.52	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (length (l ++ (1 :: l))) (snd ((f (f b 0) c), (snd (2, (length l)))))) = 
(snd ((snd ((2 * (snd (3, c))), (g (3 * c)))), (fst ((length (c :: l)), (g (g 2)))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.53" "1" ltac_term:(G)) | idtac "SSR	rand.53	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.53" "2" ltac_term:(G)) | idtac "SSR	rand.53	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.53" "3" ltac_term:(G)) | idtac "SSR	rand.53	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.53" "4" ltac_term:(G)) | idtac "SSR	rand.53	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.53" "5" ltac_term:(G)) | idtac "SSR	rand.53	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (2 * snd (3, c), g (S (S X) * c))); elpi z_report "rand.53" "6" ltac_term:(G)) | idtac "SSR	rand.53	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.53" "7" ltac_term:(G)) | idtac "SSR	rand.53	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.53" "8" ltac_term:(G)) | idtac "SSR	rand.53	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in S X); elpi z_report "rand.53" "9" ltac_term:(G)) | idtac "SSR	rand.53	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd X); elpi z_report "rand.53" "10" ltac_term:(G)) | idtac "SSR	rand.53	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (length (c :: l), g (g (S X)))); elpi z_report "rand.53" "11" ltac_term:(G)) | idtac "SSR	rand.53	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.53" "12" ltac_term:(G)) | idtac "SSR	rand.53	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = (snd ((g 3), 3)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.54" "1" ltac_term:(G)) | idtac "SSR	rand.54	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X)); elpi z_report "rand.54" "2" ltac_term:(G)) | idtac "SSR	rand.54	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.54" "3" ltac_term:(G)) | idtac "SSR	rand.54	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S (S X)); elpi z_report "rand.54" "4" ltac_term:(G)) | idtac "SSR	rand.54	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.54" "5" ltac_term:(G)) | idtac "SSR	rand.54	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.54" "6" ltac_term:(G)) | idtac "SSR	rand.54	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (g 3, S (S X))); elpi z_report "rand.54" "7" ltac_term:(G)) | idtac "SSR	rand.54	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in b = X); elpi z_report "rand.54" "8" ltac_term:(G)) | idtac "SSR	rand.54	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.54" "9" ltac_term:(G)) | idtac "SSR	rand.54	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (S (S X))); elpi z_report "rand.54" "10" ltac_term:(G)) | idtac "SSR	rand.54	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd (g 3, S (S X))); elpi z_report "rand.54" "11" ltac_term:(G)) | idtac "SSR	rand.54	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (g (S (S X)), 3)); elpi z_report "rand.54" "12" ltac_term:(G)) | idtac "SSR	rand.54	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length (0 :: l)) = 1 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (0 :: l) = X); elpi z_report "rand.55" "1" ltac_term:(G)) | idtac "SSR	rand.55	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.55" "2" ltac_term:(G)) | idtac "SSR	rand.55	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.55" "3" ltac_term:(G)) | idtac "SSR	rand.55	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in length _ = X); elpi z_report "rand.55" "4" ltac_term:(G)) | idtac "SSR	rand.55	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in length (0 :: l) = X); elpi z_report "rand.55" "5" ltac_term:(G)) | idtac "SSR	rand.55	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in length (0 :: l) = X); elpi z_report "rand.55" "6" ltac_term:(G)) | idtac "SSR	rand.55	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.55" "7" ltac_term:(G)) | idtac "SSR	rand.55	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (0 :: l) = X); elpi z_report "rand.55" "8" ltac_term:(G)) | idtac "SSR	rand.55	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in length (0 :: l) = X); elpi z_report "rand.55" "9" ltac_term:(G)) | idtac "SSR	rand.55	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.55" "10" ltac_term:(G)) | idtac "SSR	rand.55	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (_ :: _) = X); elpi z_report "rand.55" "11" ltac_term:(G)) | idtac "SSR	rand.55	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (0 :: _) = X); elpi z_report "rand.55" "12" ltac_term:(G)) | idtac "SSR	rand.55	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((g (fst (2, 1))) + ((length l) * 0)) ((length (l ++ l)) * 3)) = 0 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (g (fst (2, 1)) + length l * 0) (length (l ++ l) * S (S X)) = _); elpi z_report "rand.56" "1" ltac_term:(G)) | idtac "SSR	rand.56	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in fst (2, X)); elpi z_report "rand.56" "2" ltac_term:(G)) | idtac "SSR	rand.56	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (2, X)); elpi z_report "rand.56" "3" ltac_term:(G)) | idtac "SSR	rand.56	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in fst (X, 1)); elpi z_report "rand.56" "4" ltac_term:(G)) | idtac "SSR	rand.56	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g X); elpi z_report "rand.56" "5" ltac_term:(G)) | idtac "SSR	rand.56	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (fst (2, X)) + length l * 0); elpi z_report "rand.56" "6" ltac_term:(G)) | idtac "SSR	rand.56	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (S X, 1)); elpi z_report "rand.56" "7" ltac_term:(G)) | idtac "SSR	rand.56	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst X); elpi z_report "rand.56" "8" ltac_term:(G)) | idtac "SSR	rand.56	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (g (fst (2, X)) + length l * 0) (length (l ++ l) * 3) = _); elpi z_report "rand.56" "9" ltac_term:(G)) | idtac "SSR	rand.56	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.56" "10" ltac_term:(G)) | idtac "SSR	rand.56	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (fst (2, X)) + length l * 0); elpi z_report "rand.56" "11" ltac_term:(G)) | idtac "SSR	rand.56	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (S X, 1)); elpi z_report "rand.56" "12" ltac_term:(G)) | idtac "SSR	rand.56	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(g (length ((f 3 3) :: (0 :: l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 :: _ in X in length X); elpi z_report "rand.57" "1" ltac_term:(G)) | idtac "SSR	rand.57	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 :: _ as X in 0 = g (length (f 3 3 :: X))); elpi z_report "rand.57" "2" ltac_term:(G)) | idtac "SSR	rand.57	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 :: l as X in f 3 3 :: X); elpi z_report "rand.57" "3" ltac_term:(G)) | idtac "SSR	rand.57	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 :: _ as X in g (length (f 3 3 :: X))); elpi z_report "rand.57" "4" ltac_term:(G)) | idtac "SSR	rand.57	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (length (f 3 3 :: X))); elpi z_report "rand.57" "5" ltac_term:(G)) | idtac "SSR	rand.57	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ :: _ as X in g (length (f (S _) (S (S (S _))) :: X))); elpi z_report "rand.57" "6" ltac_term:(G)) | idtac "SSR	rand.57	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ as X in f 3 3 :: X); elpi z_report "rand.57" "7" ltac_term:(G)) | idtac "SSR	rand.57	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 :: l in X in 0 = g X); elpi z_report "rand.57" "8" ltac_term:(G)) | idtac "SSR	rand.57	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0 :: l in X in g (length X)); elpi z_report "rand.57" "9" ltac_term:(G)) | idtac "SSR	rand.57	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in f 3 3 :: X); elpi z_report "rand.57" "10" ltac_term:(G)) | idtac "SSR	rand.57	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in 0 = g X); elpi z_report "rand.57" "11" ltac_term:(G)) | idtac "SSR	rand.57	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 :: l in X in f 3 3 :: X); elpi z_report "rand.57" "12" ltac_term:(G)) | idtac "SSR	rand.57	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f a c) + (f (1 + (fst (0, 1))) (f b (g c)))) = c .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f a c + f (1 + fst (0, 1)) (f b X) = c); elpi z_report "rand.58" "1" ltac_term:(G)) | idtac "SSR	rand.58	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in f a c + f (1 + fst (0, 1)) (f b X)); elpi z_report "rand.58" "2" ltac_term:(G)) | idtac "SSR	rand.58	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.58" "3" ltac_term:(G)) | idtac "SSR	rand.58	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g c in X in f a _ + X = _); elpi z_report "rand.58" "4" ltac_term:(G)) | idtac "SSR	rand.58	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g _); elpi z_report "rand.58" "5" ltac_term:(G)) | idtac "SSR	rand.58	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in f a c + f (S _ + fst (0, 1)) (f _ X) = c); elpi z_report "rand.58" "6" ltac_term:(G)) | idtac "SSR	rand.58	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g _ as X in f (1 + fst (0, 1)) (f _ X)); elpi z_report "rand.58" "7" ltac_term:(G)) | idtac "SSR	rand.58	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in _ + f (1 + fst (0, 1)) X = c); elpi z_report "rand.58" "8" ltac_term:(G)) | idtac "SSR	rand.58	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ c + f (1 + fst (0, 1)) (f _ X)); elpi z_report "rand.58" "9" ltac_term:(G)) | idtac "SSR	rand.58	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g _); elpi z_report "rand.58" "10" ltac_term:(G)) | idtac "SSR	rand.58	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g c in X in f _ _ + f (S _ + fst (0, 1)) X); elpi z_report "rand.58" "11" ltac_term:(G)) | idtac "SSR	rand.58	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g _ as X in f a c + f (1 + fst (0, 1)) (f _ X)); elpi z_report "rand.58" "12" ltac_term:(G)) | idtac "SSR	rand.58	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((fst (3, (f (snd (2, 2)) (fst (3, a))))), c)) = 
(g ((2 + (snd (c, c))) + (f 2 (f c 2)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (2 + snd (c, c) + f (S X) (f c 2))); elpi z_report "rand.59" "1" ltac_term:(G)) | idtac "SSR	rand.59	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.59" "2" ltac_term:(G)) | idtac "SSR	rand.59	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.59" "3" ltac_term:(G)) | idtac "SSR	rand.59	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.59" "4" ltac_term:(G)) | idtac "SSR	rand.59	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (S (S X), _)); elpi z_report "rand.59" "5" ltac_term:(G)) | idtac "SSR	rand.59	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst (S X, a)); elpi z_report "rand.59" "6" ltac_term:(G)) | idtac "SSR	rand.59	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (snd (S X, 2)) (fst (3, a))); elpi z_report "rand.59" "7" ltac_term:(G)) | idtac "SSR	rand.59	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.59" "8" ltac_term:(G)) | idtac "SSR	rand.59	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (3, f (snd (2, S X)) (fst (3, a)))); elpi z_report "rand.59" "9" ltac_term:(G)) | idtac "SSR	rand.59	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f c (S X)); elpi z_report "rand.59" "10" ltac_term:(G)) | idtac "SSR	rand.59	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.59" "11" ltac_term:(G)) | idtac "SSR	rand.59	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.59" "12" ltac_term:(G)) | idtac "SSR	rand.59	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (fst (a, (length l))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in 0 = fst (a, X)); elpi z_report "rand.60" "1" ltac_term:(G)) | idtac "SSR	rand.60	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in fst X); elpi z_report "rand.60" "2" ltac_term:(G)) | idtac "SSR	rand.60	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.60" "3" ltac_term:(G)) | idtac "SSR	rand.60	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X); elpi z_report "rand.60" "4" ltac_term:(G)) | idtac "SSR	rand.60	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in 0 = fst X); elpi z_report "rand.60" "5" ltac_term:(G)) | idtac "SSR	rand.60	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.60" "6" ltac_term:(G)) | idtac "SSR	rand.60	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in fst X); elpi z_report "rand.60" "7" ltac_term:(G)) | idtac "SSR	rand.60	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in _ = fst (_, X)); elpi z_report "rand.60" "8" ltac_term:(G)) | idtac "SSR	rand.60	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.60" "9" ltac_term:(G)) | idtac "SSR	rand.60	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in fst X); elpi z_report "rand.60" "10" ltac_term:(G)) | idtac "SSR	rand.60	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.60" "11" ltac_term:(G)) | idtac "SSR	rand.60	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (a, X)); elpi z_report "rand.60" "12" ltac_term:(G)) | idtac "SSR	rand.60	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 2 = (g b) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in 2 = X); elpi z_report "rand.61" "1" ltac_term:(G)) | idtac "SSR	rand.61	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b as X in 2 = X); elpi z_report "rand.61" "2" ltac_term:(G)) | idtac "SSR	rand.61	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g _ in X in 2 = X); elpi z_report "rand.61" "3" ltac_term:(G)) | idtac "SSR	rand.61	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 2 = X); elpi z_report "rand.61" "4" ltac_term:(G)) | idtac "SSR	rand.61	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b as X in 2 = X); elpi z_report "rand.61" "5" ltac_term:(G)) | idtac "SSR	rand.61	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S _ = X); elpi z_report "rand.61" "6" ltac_term:(G)) | idtac "SSR	rand.61	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g b in X in 2 = X); elpi z_report "rand.61" "7" ltac_term:(G)) | idtac "SSR	rand.61	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.61" "8" ltac_term:(G)) | idtac "SSR	rand.61	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in S (S _) = X); elpi z_report "rand.61" "9" ltac_term:(G)) | idtac "SSR	rand.61	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b); elpi z_report "rand.61" "10" ltac_term:(G)) | idtac "SSR	rand.61	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in 2 = X); elpi z_report "rand.61" "11" ltac_term:(G)) | idtac "SSR	rand.61	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g _ as X in 2 = X); elpi z_report "rand.61" "12" ltac_term:(G)) | idtac "SSR	rand.61	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g (length l)) = (g 0) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.62" "1" ltac_term:(G)) | idtac "SSR	rand.62	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 in X in g (length l) = X); elpi z_report "rand.62" "2" ltac_term:(G)) | idtac "SSR	rand.62	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in g (length l) = X); elpi z_report "rand.62" "3" ltac_term:(G)) | idtac "SSR	rand.62	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.62" "4" ltac_term:(G)) | idtac "SSR	rand.62	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (length l) = X); elpi z_report "rand.62" "5" ltac_term:(G)) | idtac "SSR	rand.62	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in g (length l) = X); elpi z_report "rand.62" "6" ltac_term:(G)) | idtac "SSR	rand.62	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g _ = X); elpi z_report "rand.62" "7" ltac_term:(G)) | idtac "SSR	rand.62	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g 0 in X in g (length l) = X); elpi z_report "rand.62" "8" ltac_term:(G)) | idtac "SSR	rand.62	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.62" "9" ltac_term:(G)) | idtac "SSR	rand.62	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in g (length _) = X); elpi z_report "rand.62" "10" ltac_term:(G)) | idtac "SSR	rand.62	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0); elpi z_report "rand.62" "11" ltac_term:(G)) | idtac "SSR	rand.62	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in g (length l) = X); elpi z_report "rand.62" "12" ltac_term:(G)) | idtac "SSR	rand.62	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((c * (1 + a)) :: (b :: (l ++ l)))) = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (_ * X :: b :: l ++ l) = 2); elpi z_report "rand.63" "1" ltac_term:(G)) | idtac "SSR	rand.63	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = 2); elpi z_report "rand.63" "2" ltac_term:(G)) | idtac "SSR	rand.63	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c * (X + _)); elpi z_report "rand.63" "3" ltac_term:(G)) | idtac "SSR	rand.63	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (_ * (X + _) :: _ :: l ++ l)); elpi z_report "rand.63" "4" ltac_term:(G)) | idtac "SSR	rand.63	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length (X :: _ :: l ++ l)); elpi z_report "rand.63" "5" ltac_term:(G)) | idtac "SSR	rand.63	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X :: b :: l ++ l); elpi z_report "rand.63" "6" ltac_term:(G)) | idtac "SSR	rand.63	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.63" "7" ltac_term:(G)) | idtac "SSR	rand.63	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.63" "8" ltac_term:(G)) | idtac "SSR	rand.63	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.63" "9" ltac_term:(G)) | idtac "SSR	rand.63	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (c * (1 + a) :: b :: l ++ l) = X); elpi z_report "rand.63" "10" ltac_term:(G)) | idtac "SSR	rand.63	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.63" "11" ltac_term:(G)) | idtac "SSR	rand.63	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ * (X + a) :: b :: _ ++ l); elpi z_report "rand.63" "12" ltac_term:(G)) | idtac "SSR	rand.63	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (c + 0) = 
(f ((snd ((2 * 0), (f a 1))) * 2) (((length l) * (fst (2, a))) + (length (l ++ l)))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in length l * fst (2, a) + length X); elpi z_report "rand.64" "1" ltac_term:(G)) | idtac "SSR	rand.64	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.64" "2" ltac_term:(G)) | idtac "SSR	rand.64	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c + 0 = f (snd (2 * 0, f a 1) * 2) (length l * fst (2, a) + length X)); elpi z_report "rand.64" "3" ltac_term:(G)) | idtac "SSR	rand.64	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length _ * fst (2, a) + length X); elpi z_report "rand.64" "4" ltac_term:(G)) | idtac "SSR	rand.64	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in f (snd (2 * 0, f a 1) * 2) X); elpi z_report "rand.64" "5" ltac_term:(G)) | idtac "SSR	rand.64	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ l as X in length _ * fst (2, a) + length X); elpi z_report "rand.64" "6" ltac_term:(G)) | idtac "SSR	rand.64	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in c + _ = f (snd (2 * 0, f a 1) * 2) (length _ * fst (2, a) + length X)); elpi z_report "rand.64" "7" ltac_term:(G)) | idtac "SSR	rand.64	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l * fst (2, a) + length X); elpi z_report "rand.64" "8" ltac_term:(G)) | idtac "SSR	rand.64	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in length X); elpi z_report "rand.64" "9" ltac_term:(G)) | idtac "SSR	rand.64	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l * fst (2, a) + length X); elpi z_report "rand.64" "10" ltac_term:(G)) | idtac "SSR	rand.64	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c + 0 = f (snd (2 * 0, f a 1) * 2) (length l * fst (2, a) + length X)); elpi z_report "rand.64" "11" ltac_term:(G)) | idtac "SSR	rand.64	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l * fst (2, a) + length X); elpi z_report "rand.64" "12" ltac_term:(G)) | idtac "SSR	rand.64	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = _); elpi z_report "rand.65" "1" ltac_term:(G)) | idtac "SSR	rand.65	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = _); elpi z_report "rand.65" "2" ltac_term:(G)) | idtac "SSR	rand.65	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = _); elpi z_report "rand.65" "3" ltac_term:(G)) | idtac "SSR	rand.65	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = b); elpi z_report "rand.65" "4" ltac_term:(G)) | idtac "SSR	rand.65	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a = b); elpi z_report "rand.65" "5" ltac_term:(G)) | idtac "SSR	rand.65	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = _); elpi z_report "rand.65" "6" ltac_term:(G)) | idtac "SSR	rand.65	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = _); elpi z_report "rand.65" "7" ltac_term:(G)) | idtac "SSR	rand.65	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = b); elpi z_report "rand.65" "8" ltac_term:(G)) | idtac "SSR	rand.65	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a = _); elpi z_report "rand.65" "9" ltac_term:(G)) | idtac "SSR	rand.65	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = b); elpi z_report "rand.65" "10" ltac_term:(G)) | idtac "SSR	rand.65	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.65" "11" ltac_term:(G)) | idtac "SSR	rand.65	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ = _); elpi z_report "rand.65" "12" ltac_term:(G)) | idtac "SSR	rand.65	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f (g (snd (0, b))) (a + (3 * 1))) + (g (f 3 (length l)))) = 
(fst ((length ((c :: l) ++ (l ++ l))), ((snd (b, (length l))) + (fst ((snd (1, 3)), (fst (c, 1))))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (S (S X)) _); elpi z_report "rand.66" "1" ltac_term:(G)) | idtac "SSR	rand.66	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (g (snd (0, _))) (_ + S (S X) * 1)); elpi z_report "rand.66" "2" ltac_term:(G)) | idtac "SSR	rand.66	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (g (snd (0, b))) (_ + 3 * X) + g (f 3 (length l)) = fst (length ((c :: l) ++ l ++ l), snd (b, length l) + fst (snd (1, 3), fst (c, 1)))); elpi z_report "rand.66" "3" ltac_term:(G)) | idtac "SSR	rand.66	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.66" "4" ltac_term:(G)) | idtac "SSR	rand.66	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (length ((c :: l) ++ l ++ l), snd (b, length l) + fst (snd (X, 3), fst (c, 1)))); elpi z_report "rand.66" "5" ltac_term:(G)) | idtac "SSR	rand.66	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.66" "6" ltac_term:(G)) | idtac "SSR	rand.66	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (b, length l) + fst (snd (1, S (S X)), fst (c, 1))); elpi z_report "rand.66" "7" ltac_term:(G)) | idtac "SSR	rand.66	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (b, length l) + fst X); elpi z_report "rand.66" "8" ltac_term:(G)) | idtac "SSR	rand.66	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (snd (X, S (S (S _))), fst (c, 1))); elpi z_report "rand.66" "9" ltac_term:(G)) | idtac "SSR	rand.66	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (b, length l) + fst (snd (1, 3), fst (_, X))); elpi z_report "rand.66" "10" ltac_term:(G)) | idtac "SSR	rand.66	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.66" "11" ltac_term:(G)) | idtac "SSR	rand.66	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.66" "12" ltac_term:(G)) | idtac "SSR	rand.66	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((fst ((0 + 3), (f 1 b))) + (g (0 * 1))) c) = 
(c + (fst (c, (snd (1, (0 * 1)))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X _); elpi z_report "rand.67" "1" ltac_term:(G)) | idtac "SSR	rand.67	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in (_, snd (1, 0 * X))); elpi z_report "rand.67" "2" ltac_term:(G)) | idtac "SSR	rand.67	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (fst (0 + 3, f 1 b) + g (_ * X)) _ = _ + fst (c, snd (1, 0 * 1))); elpi z_report "rand.67" "3" ltac_term:(G)) | idtac "SSR	rand.67	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f (fst (0 + 3, f 1 b) + g (_ * X)) c = c + fst (c, snd (1, 0 * 1))); elpi z_report "rand.67" "4" ltac_term:(G)) | idtac "SSR	rand.67	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (fst (_ + 3, f X _) + g (0 * 1)) c); elpi z_report "rand.67" "5" ltac_term:(G)) | idtac "SSR	rand.67	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst X); elpi z_report "rand.67" "6" ltac_term:(G)) | idtac "SSR	rand.67	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in f (fst (0 + S (S X), f (S _) _) + g (_ * S _)) _ = c + fst (c, snd (1, 0 * 1))); elpi z_report "rand.67" "7" ltac_term:(G)) | idtac "SSR	rand.67	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (0 + 3, f 1 b) + g (0 * X)); elpi z_report "rand.67" "8" ltac_term:(G)) | idtac "SSR	rand.67	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in 0 * X); elpi z_report "rand.67" "9" ltac_term:(G)) | idtac "SSR	rand.67	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (0 + 3, X)); elpi z_report "rand.67" "10" ltac_term:(G)) | idtac "SSR	rand.67	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.67" "11" ltac_term:(G)) | idtac "SSR	rand.67	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (fst (0 + 3, f 1 b) + g (0 * 1)) c = c + fst (c, snd (_, 0 * X))); elpi z_report "rand.67" "12" ltac_term:(G)) | idtac "SSR	rand.67	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((fst (((fst (c, a)) + (f 3 a)), 2)), 1)) = 
((0 + 1) + (snd (3, ((fst (0, b)) * (length l))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in snd (fst (fst (c, a) + f 3 a, 2), 1) = _ + 1 + snd (3, fst (_, _) * X)); elpi z_report "rand.68" "1" ltac_term:(G)) | idtac "SSR	rand.68	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l); elpi z_report "rand.68" "2" ltac_term:(G)) | idtac "SSR	rand.68	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l in X in snd X); elpi z_report "rand.68" "3" ltac_term:(G)) | idtac "SSR	rand.68	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in snd (3, fst (0, _) * X)); elpi z_report "rand.68" "4" ltac_term:(G)) | idtac "SSR	rand.68	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in (3, X)); elpi z_report "rand.68" "5" ltac_term:(G)) | idtac "SSR	rand.68	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in 0 + 1 + snd X); elpi z_report "rand.68" "6" ltac_term:(G)) | idtac "SSR	rand.68	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in snd (3, fst (0, b) * X)); elpi z_report "rand.68" "7" ltac_term:(G)) | idtac "SSR	rand.68	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (3, fst (0, b) * X)); elpi z_report "rand.68" "8" ltac_term:(G)) | idtac "SSR	rand.68	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in snd (fst (fst (c, a) + f 3 a, 2), 1) = _ + 1 + snd X); elpi z_report "rand.68" "9" ltac_term:(G)) | idtac "SSR	rand.68	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (0, b) * X); elpi z_report "rand.68" "10" ltac_term:(G)) | idtac "SSR	rand.68	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _ in X in snd (fst (fst (c, a) + f 3 a, 2), 1) = _ + 1 + X); elpi z_report "rand.68" "11" ltac_term:(G)) | idtac "SSR	rand.68	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (0, b) * X); elpi z_report "rand.68" "12" ltac_term:(G)) | idtac "SSR	rand.68	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (((f a 3) + (fst (2, 0))) * (f (a * c) (f 3 1)))) = (g 0) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "1" ltac_term:(G)) | idtac "SSR	rand.69	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "2" ltac_term:(G)) | idtac "SSR	rand.69	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g _ in X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "3" ltac_term:(G)) | idtac "SSR	rand.69	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "4" ltac_term:(G)) | idtac "SSR	rand.69	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "5" ltac_term:(G)) | idtac "SSR	rand.69	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "6" ltac_term:(G)) | idtac "SSR	rand.69	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g ((f a 3 + fst (2, 0)) * f (_ * c) (f 3 1)) = X); elpi z_report "rand.69" "7" ltac_term:(G)) | idtac "SSR	rand.69	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.69" "8" ltac_term:(G)) | idtac "SSR	rand.69	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.69" "9" ltac_term:(G)) | idtac "SSR	rand.69	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "10" ltac_term:(G)) | idtac "SSR	rand.69	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "11" ltac_term:(G)) | idtac "SSR	rand.69	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in g ((f a 3 + fst (2, 0)) * f (a * c) (f 3 1)) = X); elpi z_report "rand.69" "12" ltac_term:(G)) | idtac "SSR	rand.69	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "1" ltac_term:(G)) | idtac "SSR	rand.70	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.70" "2" ltac_term:(G)) | idtac "SSR	rand.70	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = _); elpi z_report "rand.70" "3" ltac_term:(G)) | idtac "SSR	rand.70	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "4" ltac_term:(G)) | idtac "SSR	rand.70	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "5" ltac_term:(G)) | idtac "SSR	rand.70	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "6" ltac_term:(G)) | idtac "SSR	rand.70	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "7" ltac_term:(G)) | idtac "SSR	rand.70	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.70" "8" ltac_term:(G)) | idtac "SSR	rand.70	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "9" ltac_term:(G)) | idtac "SSR	rand.70	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "10" ltac_term:(G)) | idtac "SSR	rand.70	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = _); elpi z_report "rand.70" "11" ltac_term:(G)) | idtac "SSR	rand.70	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = b); elpi z_report "rand.70" "12" ltac_term:(G)) | idtac "SSR	rand.70	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((g (length l)) * (snd (1, 0))), (f b (snd ((f a c), c))))) = 
(length ((l ++ (2 :: l)) ++ ((3 :: l) ++ (l ++ l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in (3 :: l) ++ X); elpi z_report "rand.71" "1" ltac_term:(G)) | idtac "SSR	rand.71	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in length X); elpi z_report "rand.71" "2" ltac_term:(G)) | idtac "SSR	rand.71	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.71" "3" ltac_term:(G)) | idtac "SSR	rand.71	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in (3 :: l) ++ X); elpi z_report "rand.71" "4" ltac_term:(G)) | idtac "SSR	rand.71	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in (l ++ 2 :: l) ++ X); elpi z_report "rand.71" "5" ltac_term:(G)) | idtac "SSR	rand.71	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (3 :: l) ++ X); elpi z_report "rand.71" "6" ltac_term:(G)) | idtac "SSR	rand.71	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in length ((l ++ 2 :: l) ++ (3 :: l) ++ X)); elpi z_report "rand.71" "7" ltac_term:(G)) | idtac "SSR	rand.71	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in length ((_ ++ 2 :: _) ++ X)); elpi z_report "rand.71" "8" ltac_term:(G)) | idtac "SSR	rand.71	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in fst (g (length l) * snd (1, 0), f b (snd (f a c, c))) = length ((l ++ S (S _) :: _) ++ (3 :: _) ++ X)); elpi z_report "rand.71" "9" ltac_term:(G)) | idtac "SSR	rand.71	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((_ ++ 2 :: _) ++ (3 :: l) ++ X)); elpi z_report "rand.71" "10" ltac_term:(G)) | idtac "SSR	rand.71	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in (l ++ 2 :: l) ++ X); elpi z_report "rand.71" "11" ltac_term:(G)) | idtac "SSR	rand.71	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (3 :: l) ++ X); elpi z_report "rand.71" "12" ltac_term:(G)) | idtac "SSR	rand.71	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(2 * (snd ((g (a * c)), (snd ((snd (b, 3)), (3 * 1)))))) = 
((fst ((snd ((0 * 0), c)), ((g a) * (snd (a, b))))) * (snd (c, (fst ((2 + c), (c * b)))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c * b as X in 2 * snd (g (a * c), snd (snd (b, 3), 3 * 1)) = fst (snd (0 * 0, c), g a * snd (a, b)) * snd (_, fst (2 + c, X))); elpi z_report "rand.72" "1" ltac_term:(G)) | idtac "SSR	rand.72	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c * b in X in 2 * snd (g (a * c), snd (snd (b, 3), 3 * 1)) = fst (snd (0 * 0, c), g a * snd (a, b)) * snd (c, fst X)); elpi z_report "rand.72" "2" ltac_term:(G)) | idtac "SSR	rand.72	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in fst (2 + c, X)); elpi z_report "rand.72" "3" ltac_term:(G)) | idtac "SSR	rand.72	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 2 * snd (g (a * c), snd (snd (b, 3), 3 * 1)) = fst (snd (0 * 0, c), g a * snd (a, b)) * snd (c, fst (2 + c, X))); elpi z_report "rand.72" "4" ltac_term:(G)) | idtac "SSR	rand.72	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, fst (2 + c, X))); elpi z_report "rand.72" "5" ltac_term:(G)) | idtac "SSR	rand.72	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in 2 * snd (g (a * c), snd (snd (b, 3), 3 * 1)) = fst (snd (0 * 0, c), g a * snd (a, b)) * snd (c, fst (2 + c, X))); elpi z_report "rand.72" "6" ltac_term:(G)) | idtac "SSR	rand.72	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c * b in X in (_, X)); elpi z_report "rand.72" "7" ltac_term:(G)) | idtac "SSR	rand.72	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * b); elpi z_report "rand.72" "8" ltac_term:(G)) | idtac "SSR	rand.72	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c * b as X in fst (snd (0 * 0, c), _ * snd (a, b)) * snd (c, fst (2 + c, X))); elpi z_report "rand.72" "9" ltac_term:(G)) | idtac "SSR	rand.72	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c * _ in X in 2 * snd (g (a * c), snd (snd (b, 3), 3 * 1)) = fst (snd (0 * 0, c), g a * snd (a, b)) * snd X); elpi z_report "rand.72" "10" ltac_term:(G)) | idtac "SSR	rand.72	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 2 * snd (g (a * c), snd (snd (b, 3), 3 * 1)) = fst (snd (0 * 0, c), g a * snd (a, b)) * snd (c, fst (2 + _, X))); elpi z_report "rand.72" "11" ltac_term:(G)) | idtac "SSR	rand.72	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c * b); elpi z_report "rand.72" "12" ltac_term:(G)) | idtac "SSR	rand.72	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = 0 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = _); elpi z_report "rand.73" "1" ltac_term:(G)) | idtac "SSR	rand.73	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.73" "2" ltac_term:(G)) | idtac "SSR	rand.73	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c = 0); elpi z_report "rand.73" "3" ltac_term:(G)) | idtac "SSR	rand.73	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c = _); elpi z_report "rand.73" "4" ltac_term:(G)) | idtac "SSR	rand.73	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = 0); elpi z_report "rand.73" "5" ltac_term:(G)) | idtac "SSR	rand.73	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.73" "6" ltac_term:(G)) | idtac "SSR	rand.73	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = 0); elpi z_report "rand.73" "7" ltac_term:(G)) | idtac "SSR	rand.73	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c = _); elpi z_report "rand.73" "8" ltac_term:(G)) | idtac "SSR	rand.73	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = 0); elpi z_report "rand.73" "9" ltac_term:(G)) | idtac "SSR	rand.73	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.73" "10" ltac_term:(G)) | idtac "SSR	rand.73	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.73" "11" ltac_term:(G)) | idtac "SSR	rand.73	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = 0); elpi z_report "rand.73" "12" ltac_term:(G)) | idtac "SSR	rand.73	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (fst ((fst (c, 1)), 2)) = 
(f (f ((b + 2) * (g 1)) (fst ((g c), (g 0)))) (snd (3, ((fst (c, a)) * (b * 1))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (fst (c, 1), 2) = f (f ((b + S X) * g 1) (fst (g c, g 0))) (snd (3, fst (c, a) * (b * 1)))); elpi z_report "rand.74" "1" ltac_term:(G)) | idtac "SSR	rand.74	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.74" "2" ltac_term:(G)) | idtac "SSR	rand.74	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.74" "3" ltac_term:(G)) | idtac "SSR	rand.74	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (fst (c, 1), 2) = f (f ((b + S X) * g 1) (fst (g c, g 0))) (snd (3, fst (c, a) * (b * 1)))); elpi z_report "rand.74" "4" ltac_term:(G)) | idtac "SSR	rand.74	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (fst (c, 1), 2) = f (f ((b + 2) * g 1) (fst (g c, g 0))) (snd (S (S X), fst (c, a) * (_ * 1)))); elpi z_report "rand.74" "5" ltac_term:(G)) | idtac "SSR	rand.74	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (S _, fst (c, a) * X)); elpi z_report "rand.74" "6" ltac_term:(G)) | idtac "SSR	rand.74	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.74" "7" ltac_term:(G)) | idtac "SSR	rand.74	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g X); elpi z_report "rand.74" "8" ltac_term:(G)) | idtac "SSR	rand.74	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.74" "9" ltac_term:(G)) | idtac "SSR	rand.74	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.74" "10" ltac_term:(G)) | idtac "SSR	rand.74	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (fst (c, X), 2)); elpi z_report "rand.74" "11" ltac_term:(G)) | idtac "SSR	rand.74	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (fst (c, 1), 2) = f (f ((b + 2) * g X) (fst (g c, g 0))) (snd (3, fst (c, a) * (b * 1)))); elpi z_report "rand.74" "12" ltac_term:(G)) | idtac "SSR	rand.74	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (b, (2 + (2 + (snd (1, a)))))) = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in fst (b, 2 + (2 + snd (X, _)))); elpi z_report "rand.75" "1" ltac_term:(G)) | idtac "SSR	rand.75	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.75" "2" ltac_term:(G)) | idtac "SSR	rand.75	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.75" "3" ltac_term:(G)) | idtac "SSR	rand.75	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst (b, X)); elpi z_report "rand.75" "4" ltac_term:(G)) | idtac "SSR	rand.75	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (b, S X + (2 + snd (1, a))) = b); elpi z_report "rand.75" "5" ltac_term:(G)) | idtac "SSR	rand.75	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in fst (_, 2 + (S X + snd (1, a))) = b); elpi z_report "rand.75" "6" ltac_term:(G)) | idtac "SSR	rand.75	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + (2 + snd (1, _))); elpi z_report "rand.75" "7" ltac_term:(G)) | idtac "SSR	rand.75	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, S X + (2 + snd (1, a)))); elpi z_report "rand.75" "8" ltac_term:(G)) | idtac "SSR	rand.75	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (b, 2 + (2 + snd (X, a)))); elpi z_report "rand.75" "9" ltac_term:(G)) | idtac "SSR	rand.75	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in 2 + (2 + X)); elpi z_report "rand.75" "10" ltac_term:(G)) | idtac "SSR	rand.75	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.75" "11" ltac_term:(G)) | idtac "SSR	rand.75	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.75" "12" ltac_term:(G)) | idtac "SSR	rand.75	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (g (length l))) + c) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.76" "1" ltac_term:(G)) | idtac "SSR	rand.76	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.76" "2" ltac_term:(G)) | idtac "SSR	rand.76	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.76" "3" ltac_term:(G)) | idtac "SSR	rand.76	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.76" "4" ltac_term:(G)) | idtac "SSR	rand.76	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (g (length l)) + c = S (S X)); elpi z_report "rand.76" "5" ltac_term:(G)) | idtac "SSR	rand.76	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.76" "6" ltac_term:(G)) | idtac "SSR	rand.76	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.76" "7" ltac_term:(G)) | idtac "SSR	rand.76	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.76" "8" ltac_term:(G)) | idtac "SSR	rand.76	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X)); elpi z_report "rand.76" "9" ltac_term:(G)) | idtac "SSR	rand.76	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.76" "10" ltac_term:(G)) | idtac "SSR	rand.76	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.76" "11" ltac_term:(G)) | idtac "SSR	rand.76	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (g (length l)) + _ = S (S X)); elpi z_report "rand.76" "12" ltac_term:(G)) | idtac "SSR	rand.76	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (fst (a, 2)) = 
(f (snd (c, b)) ((g (snd (b, 3))) + (snd ((fst (1, 3)), (f a b))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f a b as X in (fst (1, 3), X)); elpi z_report "rand.77" "1" ltac_term:(G)) | idtac "SSR	rand.77	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (fst (1, 3), X)); elpi z_report "rand.77" "2" ltac_term:(G)) | idtac "SSR	rand.77	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (fst (1, 3), X)); elpi z_report "rand.77" "3" ltac_term:(G)) | idtac "SSR	rand.77	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (fst (1, 3), X)); elpi z_report "rand.77" "4" ltac_term:(G)) | idtac "SSR	rand.77	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (snd (b, 3)) + snd (fst (1, 3), X)); elpi z_report "rand.77" "5" ltac_term:(G)) | idtac "SSR	rand.77	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in fst (a, 2) = f (snd (_, b)) (g (snd (b, 3)) + snd (fst (S _, 3), X))); elpi z_report "rand.77" "6" ltac_term:(G)) | idtac "SSR	rand.77	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in fst (a, 2) = f (snd (c, _)) (g (snd (b, 3)) + snd (fst (1, 3), X))); elpi z_report "rand.77" "7" ltac_term:(G)) | idtac "SSR	rand.77	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (snd (c, b)) (g (snd (b, 3)) + snd (fst (1, 3), X))); elpi z_report "rand.77" "8" ltac_term:(G)) | idtac "SSR	rand.77	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _ in X in f (snd (c, b)) (g (snd (b, 3)) + snd X)); elpi z_report "rand.77" "9" ltac_term:(G)) | idtac "SSR	rand.77	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ b in X in (fst (1, 3), X)); elpi z_report "rand.77" "10" ltac_term:(G)) | idtac "SSR	rand.77	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ b in X in g (snd (b, 3)) + snd X); elpi z_report "rand.77" "11" ltac_term:(G)) | idtac "SSR	rand.77	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f a _); elpi z_report "rand.77" "12" ltac_term:(G)) | idtac "SSR	rand.77	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g (snd (c, (f 0 (0 * 0))))) = 
((fst ((snd ((fst (c, 0)), (f 1 0))), (length (b :: l)))) * ((f (0 * 1) (length l)) * (length (l ++ l)))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in f (0 * 1) (length l) * X); elpi z_report "rand.78" "1" ltac_term:(G)) | idtac "SSR	rand.78	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in length X); elpi z_report "rand.78" "2" ltac_term:(G)) | idtac "SSR	rand.78	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in fst (snd (fst (c, 0), f 1 0), length (b :: l)) * X); elpi z_report "rand.78" "3" ltac_term:(G)) | idtac "SSR	rand.78	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in fst (snd (fst (c, 0), f 1 0), length (b :: l)) * (f (0 * 1) _ * length X)); elpi z_report "rand.78" "4" ltac_term:(G)) | idtac "SSR	rand.78	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ l in X in fst (snd (fst (c, 0), f 1 0), length (b :: _)) * X); elpi z_report "rand.78" "5" ltac_term:(G)) | idtac "SSR	rand.78	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (snd (fst (c, 0), f 1 0), length (b :: l)) * (f (0 * 1) (length l) * length X)); elpi z_report "rand.78" "6" ltac_term:(G)) | idtac "SSR	rand.78	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ _); elpi z_report "rand.78" "7" ltac_term:(G)) | idtac "SSR	rand.78	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in f (0 * 1) (length l) * length X); elpi z_report "rand.78" "8" ltac_term:(G)) | idtac "SSR	rand.78	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in f (_ * 1) (length l) * length X); elpi z_report "rand.78" "9" ltac_term:(G)) | idtac "SSR	rand.78	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.78" "10" ltac_term:(G)) | idtac "SSR	rand.78	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ l in X in fst (snd (fst (c, 0), f 1 0), length (b :: l)) * X); elpi z_report "rand.78" "11" ltac_term:(G)) | idtac "SSR	rand.78	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in fst (snd (fst (c, 0), f 1 0), length (b :: l)) * (f (0 * 1) (length l) * length X)); elpi z_report "rand.78" "12" ltac_term:(G)) | idtac "SSR	rand.78	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(3 + (snd (2, ((f a 2) * (length l))))) = a .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.79" "1" ltac_term:(G)) | idtac "SSR	rand.79	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in 3 + snd (2, f a 2 * X)); elpi z_report "rand.79" "2" ltac_term:(G)) | idtac "SSR	rand.79	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in snd (2, f a 2 * X)); elpi z_report "rand.79" "3" ltac_term:(G)) | idtac "SSR	rand.79	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.79" "4" ltac_term:(G)) | idtac "SSR	rand.79	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in (2, X)); elpi z_report "rand.79" "5" ltac_term:(G)) | idtac "SSR	rand.79	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in 3 + snd (2, X)); elpi z_report "rand.79" "6" ltac_term:(G)) | idtac "SSR	rand.79	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in 3 + snd X); elpi z_report "rand.79" "7" ltac_term:(G)) | idtac "SSR	rand.79	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 + snd (2, f a 2 * X) = a); elpi z_report "rand.79" "8" ltac_term:(G)) | idtac "SSR	rand.79	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l as X in 3 + snd (2, f a 2 * X)); elpi z_report "rand.79" "9" ltac_term:(G)) | idtac "SSR	rand.79	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 + snd (2, f a 2 * X) = a); elpi z_report "rand.79" "10" ltac_term:(G)) | idtac "SSR	rand.79	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 + snd (2, f a 2 * X) = a); elpi z_report "rand.79" "11" ltac_term:(G)) | idtac "SSR	rand.79	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in snd (2, X)); elpi z_report "rand.79" "12" ltac_term:(G)) | idtac "SSR	rand.79	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), ((g 1) + c) = 
(length ((f (a + c) 1) :: ((0 + 0) :: (l ++ l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (a + _) 1 :: 0 + 0 :: X); elpi z_report "rand.80" "1" ltac_term:(G)) | idtac "SSR	rand.80	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.80" "2" ltac_term:(G)) | idtac "SSR	rand.80	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.80" "3" ltac_term:(G)) | idtac "SSR	rand.80	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in 0 + 0 :: X); elpi z_report "rand.80" "4" ltac_term:(G)) | idtac "SSR	rand.80	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in g 1 + c = length (f (a + c) 1 :: _ + 0 :: X)); elpi z_report "rand.80" "5" ltac_term:(G)) | idtac "SSR	rand.80	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.80" "6" ltac_term:(G)) | idtac "SSR	rand.80	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g 1 + c = length (f (a + c) 1 :: 0 + 0 :: X)); elpi z_report "rand.80" "7" ltac_term:(G)) | idtac "SSR	rand.80	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in length (f (a + _) 1 :: 0 + 0 :: X)); elpi z_report "rand.80" "8" ltac_term:(G)) | idtac "SSR	rand.80	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (f (a + c) 1 :: 0 + 0 :: X)); elpi z_report "rand.80" "9" ltac_term:(G)) | idtac "SSR	rand.80	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in g 1 + c = length (f (a + c) 1 :: X)); elpi z_report "rand.80" "10" ltac_term:(G)) | idtac "SSR	rand.80	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g 1 + c = length (f (a + c) 1 :: 0 + 0 :: X)); elpi z_report "rand.80" "11" ltac_term:(G)) | idtac "SSR	rand.80	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in g 1 + c = length (f (a + c) 1 :: X)); elpi z_report "rand.80" "12" ltac_term:(G)) | idtac "SSR	rand.80	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (snd ((snd ((g b), 1)), 2)) ((snd (c, (length l))) * ((snd (a, 2)) + (3 * 3)))) 
= 
(f (fst (2, (f (fst (2, 0)) (snd (2, c))))) (fst (c, (fst ((snd (b, 3)), (g 1)))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.81" "1" ltac_term:(G)) | idtac "SSR	rand.81	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (_, X)); elpi z_report "rand.81" "2" ltac_term:(G)) | idtac "SSR	rand.81	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (a, 2) + X); elpi z_report "rand.81" "3" ltac_term:(G)) | idtac "SSR	rand.81	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in f (snd X) (snd (c, length l) * (snd (a, 2) + 3 * 3))); elpi z_report "rand.81" "4" ltac_term:(G)) | idtac "SSR	rand.81	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in (_, fst (snd (b, 3), g X))); elpi z_report "rand.81" "5" ltac_term:(G)) | idtac "SSR	rand.81	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst (snd (_, X), g 1)); elpi z_report "rand.81" "6" ltac_term:(G)) | idtac "SSR	rand.81	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in snd (_, X)); elpi z_report "rand.81" "7" ltac_term:(G)) | idtac "SSR	rand.81	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in snd (X, _)); elpi z_report "rand.81" "8" ltac_term:(G)) | idtac "SSR	rand.81	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (g b, X)); elpi z_report "rand.81" "9" ltac_term:(G)) | idtac "SSR	rand.81	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (snd (X, 2)) (snd (c, length l) * (snd (a, 2) + 3 * 3))); elpi z_report "rand.81" "10" ltac_term:(G)) | idtac "SSR	rand.81	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (S X, _)); elpi z_report "rand.81" "11" ltac_term:(G)) | idtac "SSR	rand.81	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.81" "12" ltac_term:(G)) | idtac "SSR	rand.81	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((length (l ++ l)), (f c (fst (a, b))))) * (((0 + a) * (b + c)) + ((a + 0) + (2 + 0)))) 
= c .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X + _); elpi z_report "rand.82" "1" ltac_term:(G)) | idtac "SSR	rand.82	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in fst (length (l ++ l), f c (fst (a, b))) * ((_ + a) * (b + _) + (_ + 0 + (S X + 0))) = _); elpi z_report "rand.82" "2" ltac_term:(G)) | idtac "SSR	rand.82	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.82" "3" ltac_term:(G)) | idtac "SSR	rand.82	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.82" "4" ltac_term:(G)) | idtac "SSR	rand.82	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in fst (length (l ++ l), f c (fst (a, b))) * ((0 + a) * (b + c) + X) = _); elpi z_report "rand.82" "5" ltac_term:(G)) | idtac "SSR	rand.82	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.82" "6" ltac_term:(G)) | idtac "SSR	rand.82	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in fst (length (l ++ l), f c (fst (a, b))) * ((0 + a) * (b + c) + (a + 0 + (S X + 0)))); elpi z_report "rand.82" "7" ltac_term:(G)) | idtac "SSR	rand.82	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + 0); elpi z_report "rand.82" "8" ltac_term:(G)) | idtac "SSR	rand.82	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in fst (length (l ++ l), f c (fst (a, b))) * ((0 + a) * (b + c) + X) = c); elpi z_report "rand.82" "9" ltac_term:(G)) | idtac "SSR	rand.82	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X + 0); elpi z_report "rand.82" "10" ltac_term:(G)) | idtac "SSR	rand.82	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in a + _ + X); elpi z_report "rand.82" "11" ltac_term:(G)) | idtac "SSR	rand.82	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.82" "12" ltac_term:(G)) | idtac "SSR	rand.82	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (a + 1) = 
((fst (((g a) * (a + 0)), b)) + c) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "rand.83" "1" ltac_term:(G)) | idtac "SSR	rand.83	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _); elpi z_report "rand.83" "2" ltac_term:(G)) | idtac "SSR	rand.83	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (_ * X, _)); elpi z_report "rand.83" "3" ltac_term:(G)) | idtac "SSR	rand.83	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g a * X, b)); elpi z_report "rand.83" "4" ltac_term:(G)) | idtac "SSR	rand.83	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ + 0 in X in a + 1 = X + c); elpi z_report "rand.83" "5" ltac_term:(G)) | idtac "SSR	rand.83	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ as X in g a * X); elpi z_report "rand.83" "6" ltac_term:(G)) | idtac "SSR	rand.83	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in a + 1 = fst (X, b) + _); elpi z_report "rand.83" "7" ltac_term:(G)) | idtac "SSR	rand.83	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g a * X, b) + _); elpi z_report "rand.83" "8" ltac_term:(G)) | idtac "SSR	rand.83	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g a * X, b)); elpi z_report "rand.83" "9" ltac_term:(G)) | idtac "SSR	rand.83	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in fst (X, b) + c); elpi z_report "rand.83" "10" ltac_term:(G)) | idtac "SSR	rand.83	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in (X, _)); elpi z_report "rand.83" "11" ltac_term:(G)) | idtac "SSR	rand.83	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + 0); elpi z_report "rand.83" "12" ltac_term:(G)) | idtac "SSR	rand.83	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (((snd (c, 0)) :: l) ++ (l ++ (l ++ l)))) = 
((g (f 2 (length l))) * ((fst (b, b)) + (length (l ++ l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ _ in X in l ++ X); elpi z_report "rand.84" "1" ltac_term:(G)) | idtac "SSR	rand.84	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.84" "2" ltac_term:(G)) | idtac "SSR	rand.84	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l as X in g (f 2 (length l)) * (fst (b, b) + length X)); elpi z_report "rand.84" "3" ltac_term:(G)) | idtac "SSR	rand.84	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((snd (c, 0) :: l) ++ l ++ X)); elpi z_report "rand.84" "4" ltac_term:(G)) | idtac "SSR	rand.84	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in length X); elpi z_report "rand.84" "5" ltac_term:(G)) | idtac "SSR	rand.84	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ _ in X in fst (b, b) + X); elpi z_report "rand.84" "6" ltac_term:(G)) | idtac "SSR	rand.84	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ ++ X); elpi z_report "rand.84" "7" ltac_term:(G)) | idtac "SSR	rand.84	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length ((snd (c, 0) :: _) ++ _ ++ X) = g (f 2 (length l)) * (fst (b, b) + length (l ++ l))); elpi z_report "rand.84" "8" ltac_term:(G)) | idtac "SSR	rand.84	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.84" "9" ltac_term:(G)) | idtac "SSR	rand.84	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ l in X in _ ++ X); elpi z_report "rand.84" "10" ltac_term:(G)) | idtac "SSR	rand.84	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ l as X in fst (b, b) + length X); elpi z_report "rand.84" "11" ltac_term:(G)) | idtac "SSR	rand.84	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in length ((snd (c, 0) :: l) ++ _ ++ X)); elpi z_report "rand.84" "12" ltac_term:(G)) | idtac "SSR	rand.84	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = (length l) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in b = X); elpi z_report "rand.85" "1" ltac_term:(G)) | idtac "SSR	rand.85	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.85" "2" ltac_term:(G)) | idtac "SSR	rand.85	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.85" "3" ltac_term:(G)) | idtac "SSR	rand.85	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b = X); elpi z_report "rand.85" "4" ltac_term:(G)) | idtac "SSR	rand.85	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.85" "5" ltac_term:(G)) | idtac "SSR	rand.85	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "rand.85" "6" ltac_term:(G)) | idtac "SSR	rand.85	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in b = X); elpi z_report "rand.85" "7" ltac_term:(G)) | idtac "SSR	rand.85	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in b = X); elpi z_report "rand.85" "8" ltac_term:(G)) | idtac "SSR	rand.85	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in b = X); elpi z_report "rand.85" "9" ltac_term:(G)) | idtac "SSR	rand.85	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l as X in _ = X); elpi z_report "rand.85" "10" ltac_term:(G)) | idtac "SSR	rand.85	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l in X in b = X); elpi z_report "rand.85" "11" ltac_term:(G)) | idtac "SSR	rand.85	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.85" "12" ltac_term:(G)) | idtac "SSR	rand.85	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((snd ((f (snd (c, 0)) 3), (snd ((f 1 0), (snd (2, 2)))))), (c * ((g 2) + (snd (a, 0)))))) 
= 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in S X); elpi z_report "rand.86" "1" ltac_term:(G)) | idtac "SSR	rand.86	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in (X, c * (g 2 + snd (a, _)))); elpi z_report "rand.86" "2" ltac_term:(G)) | idtac "SSR	rand.86	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.86" "3" ltac_term:(G)) | idtac "SSR	rand.86	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.86" "4" ltac_term:(G)) | idtac "SSR	rand.86	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (snd (f (snd (c, 0)) 3, X), c * (g 2 + snd (a, 0)))); elpi z_report "rand.86" "5" ltac_term:(G)) | idtac "SSR	rand.86	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.86" "6" ltac_term:(G)) | idtac "SSR	rand.86	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.86" "7" ltac_term:(G)) | idtac "SSR	rand.86	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ * (g X + snd (a, 0))); elpi z_report "rand.86" "8" ltac_term:(G)) | idtac "SSR	rand.86	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in snd (snd (f (snd (c, 0)) 3, snd (f X 0, snd (2, 2))), c * (g 2 + snd (a, 0)))); elpi z_report "rand.86" "9" ltac_term:(G)) | idtac "SSR	rand.86	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in c * (g X + snd (_, _))); elpi z_report "rand.86" "10" ltac_term:(G)) | idtac "SSR	rand.86	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (X, snd (2, 2))); elpi z_report "rand.86" "11" ltac_term:(G)) | idtac "SSR	rand.86	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.86" "12" ltac_term:(G)) | idtac "SSR	rand.86	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g ((a + 0) + (snd (b, (length l))))) = 
(((snd (3, (g 0))) * (fst ((length l), (a * c)))) * (length ((1 + 3) :: (l ++ l)))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (3, g 0) * fst (length l, a * c) * length (1 + 3 :: X)); elpi z_report "rand.87" "1" ltac_term:(G)) | idtac "SSR	rand.87	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + 3 :: X); elpi z_report "rand.87" "2" ltac_term:(G)) | idtac "SSR	rand.87	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.87" "3" ltac_term:(G)) | idtac "SSR	rand.87	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in length (1 + 3 :: X)); elpi z_report "rand.87" "4" ltac_term:(G)) | idtac "SSR	rand.87	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (1 + 3 :: X)); elpi z_report "rand.87" "5" ltac_term:(G)) | idtac "SSR	rand.87	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.87" "6" ltac_term:(G)) | idtac "SSR	rand.87	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in snd (3, g 0) * fst (length l, a * c) * X); elpi z_report "rand.87" "7" ltac_term:(G)) | idtac "SSR	rand.87	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in length X); elpi z_report "rand.87" "8" ltac_term:(G)) | idtac "SSR	rand.87	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.87" "9" ltac_term:(G)) | idtac "SSR	rand.87	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.87" "10" ltac_term:(G)) | idtac "SSR	rand.87	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ l in X in g (a + 0 + snd (b, length l)) = snd (3, g 0) * fst (length l, a * c) * X); elpi z_report "rand.87" "11" ltac_term:(G)) | idtac "SSR	rand.87	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ l in X in length X); elpi z_report "rand.87" "12" ltac_term:(G)) | idtac "SSR	rand.87	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g 1) = 
(snd ((3 + (length (l ++ l))), (g (length (l ++ l))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (length X)); elpi z_report "rand.88" "1" ltac_term:(G)) | idtac "SSR	rand.88	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in length X); elpi z_report "rand.88" "2" ltac_term:(G)) | idtac "SSR	rand.88	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X); elpi z_report "rand.88" "3" ltac_term:(G)) | idtac "SSR	rand.88	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd (3 + length X, g (length (l ++ l)))); elpi z_report "rand.88" "4" ltac_term:(G)) | idtac "SSR	rand.88	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ l in X in length X); elpi z_report "rand.88" "5" ltac_term:(G)) | idtac "SSR	rand.88	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (3 + length (l ++ l), g (length X))); elpi z_report "rand.88" "6" ltac_term:(G)) | idtac "SSR	rand.88	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (3 + length (l ++ l), g (length X))); elpi z_report "rand.88" "7" ltac_term:(G)) | idtac "SSR	rand.88	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.88" "8" ltac_term:(G)) | idtac "SSR	rand.88	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in 3 + length X); elpi z_report "rand.88" "9" ltac_term:(G)) | idtac "SSR	rand.88	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l as X in g (length X)); elpi z_report "rand.88" "10" ltac_term:(G)) | idtac "SSR	rand.88	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd (3 + length X, g (length (l ++ l)))); elpi z_report "rand.88" "11" ltac_term:(G)) | idtac "SSR	rand.88	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X); elpi z_report "rand.88" "12" ltac_term:(G)) | idtac "SSR	rand.88	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = (f 0 c) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 _ in X in _ = X); elpi z_report "rand.89" "1" ltac_term:(G)) | idtac "SSR	rand.89	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ c); elpi z_report "rand.89" "2" ltac_term:(G)) | idtac "SSR	rand.89	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c = X); elpi z_report "rand.89" "3" ltac_term:(G)) | idtac "SSR	rand.89	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c = X); elpi z_report "rand.89" "4" ltac_term:(G)) | idtac "SSR	rand.89	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _ in X in _ = X); elpi z_report "rand.89" "5" ltac_term:(G)) | idtac "SSR	rand.89	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 c in X in c = X); elpi z_report "rand.89" "6" ltac_term:(G)) | idtac "SSR	rand.89	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 c as X in c = X); elpi z_report "rand.89" "7" ltac_term:(G)) | idtac "SSR	rand.89	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "rand.89" "8" ltac_term:(G)) | idtac "SSR	rand.89	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ c in X in _ = X); elpi z_report "rand.89" "9" ltac_term:(G)) | idtac "SSR	rand.89	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ c); elpi z_report "rand.89" "10" ltac_term:(G)) | idtac "SSR	rand.89	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c = X); elpi z_report "rand.89" "11" ltac_term:(G)) | idtac "SSR	rand.89	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ c in X in c = X); elpi z_report "rand.89" "12" ltac_term:(G)) | idtac "SSR	rand.89	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((((length l) * (2 * 1)) * (f (b + 0) (fst (1, 3)))) * (length l)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.90" "1" ltac_term:(G)) | idtac "SSR	rand.90	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _); elpi z_report "rand.90" "2" ltac_term:(G)) | idtac "SSR	rand.90	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l as X in X = length l * (2 * 1) * f (b + 0) (fst (1, 3)) * length l); elpi z_report "rand.90" "3" ltac_term:(G)) | idtac "SSR	rand.90	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l = length l * (2 * 1) * f (b + 0) (fst (1, 3)) * X); elpi z_report "rand.90" "4" ltac_term:(G)) | idtac "SSR	rand.90	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X); elpi z_report "rand.90" "5" ltac_term:(G)) | idtac "SSR	rand.90	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in length l * (2 * 1) * f (b + 0) (fst (1, 3)) * X); elpi z_report "rand.90" "6" ltac_term:(G)) | idtac "SSR	rand.90	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.90" "7" ltac_term:(G)) | idtac "SSR	rand.90	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in X * (2 * 1)); elpi z_report "rand.90" "8" ltac_term:(G)) | idtac "SSR	rand.90	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length _ * (2 * 1) * f (b + 0) (fst (1, 3)) * X); elpi z_report "rand.90" "9" ltac_term:(G)) | idtac "SSR	rand.90	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.90" "10" ltac_term:(G)) | idtac "SSR	rand.90	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in X = length l * (2 * 1) * f (b + 0) (fst (1, 3)) * length l); elpi z_report "rand.90" "11" ltac_term:(G)) | idtac "SSR	rand.90	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l * (2 * 1) * f (b + 0) (fst (1, 3)) * X); elpi z_report "rand.90" "12" ltac_term:(G)) | idtac "SSR	rand.90	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ = _); elpi z_report "rand.91" "1" ltac_term:(G)) | idtac "SSR	rand.91	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = b); elpi z_report "rand.91" "2" ltac_term:(G)) | idtac "SSR	rand.91	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a = _); elpi z_report "rand.91" "3" ltac_term:(G)) | idtac "SSR	rand.91	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ = _); elpi z_report "rand.91" "4" ltac_term:(G)) | idtac "SSR	rand.91	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.91" "5" ltac_term:(G)) | idtac "SSR	rand.91	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.91" "6" ltac_term:(G)) | idtac "SSR	rand.91	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = b); elpi z_report "rand.91" "7" ltac_term:(G)) | idtac "SSR	rand.91	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.91" "8" ltac_term:(G)) | idtac "SSR	rand.91	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a = _); elpi z_report "rand.91" "9" ltac_term:(G)) | idtac "SSR	rand.91	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.91" "10" ltac_term:(G)) | idtac "SSR	rand.91	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.91" "11" ltac_term:(G)) | idtac "SSR	rand.91	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.91" "12" ltac_term:(G)) | idtac "SSR	rand.91	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((f (f c 2) ((0 * 2) * (0 * 0))), ((f (snd (c, 3)) 1) + (g 3)))) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.92" "1" ltac_term:(G)) | idtac "SSR	rand.92	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (f (f c 2) X, f (snd (c, 3)) 1 + g 3) = 3); elpi z_report "rand.92" "2" ltac_term:(G)) | idtac "SSR	rand.92	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (snd (c, 3)) X); elpi z_report "rand.92" "3" ltac_term:(G)) | idtac "SSR	rand.92	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.92" "4" ltac_term:(G)) | idtac "SSR	rand.92	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in snd (f (f c 2) (0 * 2 * (0 * 0)), f (snd (c, 3)) 1 + X) = 3); elpi z_report "rand.92" "5" ltac_term:(G)) | idtac "SSR	rand.92	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (snd (c, 3)) 1 + g (S (S X))); elpi z_report "rand.92" "6" ltac_term:(G)) | idtac "SSR	rand.92	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.92" "7" ltac_term:(G)) | idtac "SSR	rand.92	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (snd (_, S (S X))) _); elpi z_report "rand.92" "8" ltac_term:(G)) | idtac "SSR	rand.92	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.92" "9" ltac_term:(G)) | idtac "SSR	rand.92	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (snd (c, 3)) X); elpi z_report "rand.92" "10" ltac_term:(G)) | idtac "SSR	rand.92	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.92" "11" ltac_term:(G)) | idtac "SSR	rand.92	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (f (f c 2) (0 * 2 * (0 * 0)), f (snd (c, 3)) X + g (S (S _))) = 3); elpi z_report "rand.92" "12" ltac_term:(G)) | idtac "SSR	rand.92	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((g (fst ((1 * 3), (g 3)))) + (f 2 2)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.93" "1" ltac_term:(G)) | idtac "SSR	rand.93	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (X * S _, g 3)); elpi z_report "rand.93" "2" ltac_term:(G)) | idtac "SSR	rand.93	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g (fst (1 * 3, g 3)) + f 2 X); elpi z_report "rand.93" "3" ltac_term:(G)) | idtac "SSR	rand.93	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (fst (1 * S (S X), g 3))); elpi z_report "rand.93" "4" ltac_term:(G)) | idtac "SSR	rand.93	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.93" "5" ltac_term:(G)) | idtac "SSR	rand.93	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 = g (fst (1 * S (S X), g 3)) + f 2 2); elpi z_report "rand.93" "6" ltac_term:(G)) | idtac "SSR	rand.93	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.93" "7" ltac_term:(G)) | idtac "SSR	rand.93	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.93" "8" ltac_term:(G)) | idtac "SSR	rand.93	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g (fst (X, g 3)) + f 2 2); elpi z_report "rand.93" "9" ltac_term:(G)) | idtac "SSR	rand.93	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in X = g (fst (_ * 3, g 3)) + f 2 2); elpi z_report "rand.93" "10" ltac_term:(G)) | idtac "SSR	rand.93	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _); elpi z_report "rand.93" "11" ltac_term:(G)) | idtac "SSR	rand.93	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.93" "12" ltac_term:(G)) | idtac "SSR	rand.93	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 = b); elpi z_report "rand.94" "1" ltac_term:(G)) | idtac "SSR	rand.94	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.94" "2" ltac_term:(G)) | idtac "SSR	rand.94	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 = b); elpi z_report "rand.94" "3" ltac_term:(G)) | idtac "SSR	rand.94	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 = _); elpi z_report "rand.94" "4" ltac_term:(G)) | idtac "SSR	rand.94	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 = b); elpi z_report "rand.94" "5" ltac_term:(G)) | idtac "SSR	rand.94	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.94" "6" ltac_term:(G)) | idtac "SSR	rand.94	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 = _); elpi z_report "rand.94" "7" ltac_term:(G)) | idtac "SSR	rand.94	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0 = b); elpi z_report "rand.94" "8" ltac_term:(G)) | idtac "SSR	rand.94	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0 = b); elpi z_report "rand.94" "9" ltac_term:(G)) | idtac "SSR	rand.94	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 = b); elpi z_report "rand.94" "10" ltac_term:(G)) | idtac "SSR	rand.94	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = b); elpi z_report "rand.94" "11" ltac_term:(G)) | idtac "SSR	rand.94	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = b); elpi z_report "rand.94" "12" ltac_term:(G)) | idtac "SSR	rand.94	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((g b) * (2 + (fst ((fst (3, 2)), 1)))) = 
(g ((length (l ++ l)) * (fst (a, 1)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g b * (X + fst (fst (3, 2), 1))); elpi z_report "rand.95" "1" ltac_term:(G)) | idtac "SSR	rand.95	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in S X); elpi z_report "rand.95" "2" ltac_term:(G)) | idtac "SSR	rand.95	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (length (l ++ l) * fst (_, X))); elpi z_report "rand.95" "3" ltac_term:(G)) | idtac "SSR	rand.95	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g b * (2 + fst (fst (3, S X), 1))); elpi z_report "rand.95" "4" ltac_term:(G)) | idtac "SSR	rand.95	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (fst (3, 2), X)); elpi z_report "rand.95" "5" ltac_term:(G)) | idtac "SSR	rand.95	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in 2 + fst (fst (3, S X), 1)); elpi z_report "rand.95" "6" ltac_term:(G)) | idtac "SSR	rand.95	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, X)); elpi z_report "rand.95" "7" ltac_term:(G)) | idtac "SSR	rand.95	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.95" "8" ltac_term:(G)) | idtac "SSR	rand.95	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (3, S X)); elpi z_report "rand.95" "9" ltac_term:(G)) | idtac "SSR	rand.95	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.95" "10" ltac_term:(G)) | idtac "SSR	rand.95	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (fst (3, 2), X)); elpi z_report "rand.95" "11" ltac_term:(G)) | idtac "SSR	rand.95	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (fst (S (S X), 2), 1)); elpi z_report "rand.95" "12" ltac_term:(G)) | idtac "SSR	rand.95	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (a * 3) = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * S (S X)); elpi z_report "rand.96" "1" ltac_term:(G)) | idtac "SSR	rand.96	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.96" "2" ltac_term:(G)) | idtac "SSR	rand.96	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.96" "3" ltac_term:(G)) | idtac "SSR	rand.96	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in S (S X)); elpi z_report "rand.96" "4" ltac_term:(G)) | idtac "SSR	rand.96	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in a * S (S X) = b); elpi z_report "rand.96" "5" ltac_term:(G)) | idtac "SSR	rand.96	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.96" "6" ltac_term:(G)) | idtac "SSR	rand.96	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ * S (S X)); elpi z_report "rand.96" "7" ltac_term:(G)) | idtac "SSR	rand.96	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S (S X)); elpi z_report "rand.96" "8" ltac_term:(G)) | idtac "SSR	rand.96	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.96" "9" ltac_term:(G)) | idtac "SSR	rand.96	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in a * S (S X)); elpi z_report "rand.96" "10" ltac_term:(G)) | idtac "SSR	rand.96	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.96" "11" ltac_term:(G)) | idtac "SSR	rand.96	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.96" "12" ltac_term:(G)) | idtac "SSR	rand.96	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 
(snd ((f 1 (snd (0, (g c)))), (f (length l) (snd ((3 * 2), c))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd (S (S X) * 2, c)); elpi z_report "rand.97" "1" ltac_term:(G)) | idtac "SSR	rand.97	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in S X); elpi z_report "rand.97" "2" ltac_term:(G)) | idtac "SSR	rand.97	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S (S X)); elpi z_report "rand.97" "3" ltac_term:(G)) | idtac "SSR	rand.97	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (S (S X) * 2, c)); elpi z_report "rand.97" "4" ltac_term:(G)) | idtac "SSR	rand.97	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S (S _) * X); elpi z_report "rand.97" "5" ltac_term:(G)) | idtac "SSR	rand.97	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.97" "6" ltac_term:(G)) | idtac "SSR	rand.97	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.97" "7" ltac_term:(G)) | idtac "SSR	rand.97	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in f X (snd (0, g c))); elpi z_report "rand.97" "8" ltac_term:(G)) | idtac "SSR	rand.97	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (f X (snd (_, _)), f (length l) (snd (3 * 2, c)))); elpi z_report "rand.97" "9" ltac_term:(G)) | idtac "SSR	rand.97	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.97" "10" ltac_term:(G)) | idtac "SSR	rand.97	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (f X (snd (_, g c)), f (length l) (snd (3 * 2, c)))); elpi z_report "rand.97" "11" ltac_term:(G)) | idtac "SSR	rand.97	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.97" "12" ltac_term:(G)) | idtac "SSR	rand.97	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((g (g (length l))), (f (g (c * 2)) a))) = 
(snd (b, ((fst ((f 0 c), (2 + 0))) * (length (l ++ l))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in snd (b, fst (f 0 c, 2 + 0) * length X)); elpi z_report "rand.98" "1" ltac_term:(G)) | idtac "SSR	rand.98	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ _ in X in fst (g (g (length l)), f (g (c * 2)) a) = snd X); elpi z_report "rand.98" "2" ltac_term:(G)) | idtac "SSR	rand.98	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in fst (f 0 c, 2 + 0) * X); elpi z_report "rand.98" "3" ltac_term:(G)) | idtac "SSR	rand.98	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f 0 c, 2 + 0) * length X); elpi z_report "rand.98" "4" ltac_term:(G)) | idtac "SSR	rand.98	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (b, fst (f 0 c, 2 + 0) * length X)); elpi z_report "rand.98" "5" ltac_term:(G)) | idtac "SSR	rand.98	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in (_, fst (f 0 c, 2 + 0) * length X)); elpi z_report "rand.98" "6" ltac_term:(G)) | idtac "SSR	rand.98	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in fst (f 0 c, 2 + 0) * X); elpi z_report "rand.98" "7" ltac_term:(G)) | idtac "SSR	rand.98	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in fst (f 0 c, 2 + 0) * length X); elpi z_report "rand.98" "8" ltac_term:(G)) | idtac "SSR	rand.98	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g (g (length l)), f (g (c * 2)) a) = snd (_, fst (f 0 c, 2 + 0) * length X)); elpi z_report "rand.98" "9" ltac_term:(G)) | idtac "SSR	rand.98	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ _ in X in fst (f 0 c, 2 + 0) * X); elpi z_report "rand.98" "10" ltac_term:(G)) | idtac "SSR	rand.98	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(l ++ _ as X in length X); elpi z_report "rand.98" "11" ltac_term:(G)) | idtac "SSR	rand.98	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ _ in X in snd X); elpi z_report "rand.98" "12" ltac_term:(G)) | idtac "SSR	rand.98	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g (f 3 (length l))) = c .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in g X); elpi z_report "rand.99" "1" ltac_term:(G)) | idtac "SSR	rand.99	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in f 3 X); elpi z_report "rand.99" "2" ltac_term:(G)) | idtac "SSR	rand.99	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.99" "3" ltac_term:(G)) | idtac "SSR	rand.99	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (S (S _)) X); elpi z_report "rand.99" "4" ltac_term:(G)) | idtac "SSR	rand.99	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in f 3 X); elpi z_report "rand.99" "5" ltac_term:(G)) | idtac "SSR	rand.99	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.99" "6" ltac_term:(G)) | idtac "SSR	rand.99	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f 3 X); elpi z_report "rand.99" "7" ltac_term:(G)) | idtac "SSR	rand.99	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f 3 X); elpi z_report "rand.99" "8" ltac_term:(G)) | idtac "SSR	rand.99	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in f 3 X); elpi z_report "rand.99" "9" ltac_term:(G)) | idtac "SSR	rand.99	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.99" "10" ltac_term:(G)) | idtac "SSR	rand.99	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in g (f 3 X) = c); elpi z_report "rand.99" "11" ltac_term:(G)) | idtac "SSR	rand.99	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.99" "12" ltac_term:(G)) | idtac "SSR	rand.99	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst ((snd ((snd (c, 0)), c)), (length (c :: l)))) + 2) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.100" "1" ltac_term:(G)) | idtac "SSR	rand.100	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst (snd (snd (c, 0), _), length (c :: l)) + X); elpi z_report "rand.100" "2" ltac_term:(G)) | idtac "SSR	rand.100	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.100" "3" ltac_term:(G)) | idtac "SSR	rand.100	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (snd (snd (c, 0), c), length (c :: l)) + 2 = S (S X)); elpi z_report "rand.100" "4" ltac_term:(G)) | idtac "SSR	rand.100	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.100" "5" ltac_term:(G)) | idtac "SSR	rand.100	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (snd (snd (c, 0), c), length (c :: l)) + S X); elpi z_report "rand.100" "6" ltac_term:(G)) | idtac "SSR	rand.100	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (snd (snd (c, 0), c), length (_ :: l)) + S X); elpi z_report "rand.100" "7" ltac_term:(G)) | idtac "SSR	rand.100	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (snd (snd (c, 0), c), length _) + S X); elpi z_report "rand.100" "8" ltac_term:(G)) | idtac "SSR	rand.100	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in fst (snd (snd (c, 0), c), length (c :: l)) + 2 = X); elpi z_report "rand.100" "9" ltac_term:(G)) | idtac "SSR	rand.100	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in fst (snd (snd (c, 0), c), length (c :: l)) + X); elpi z_report "rand.100" "10" ltac_term:(G)) | idtac "SSR	rand.100	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst (snd (snd (c, 0), c), length (c :: l)) + X); elpi z_report "rand.100" "11" ltac_term:(G)) | idtac "SSR	rand.100	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.100" "12" ltac_term:(G)) | idtac "SSR	rand.100	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = (length l) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.101" "1" ltac_term:(G)) | idtac "SSR	rand.101	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in b = X); elpi z_report "rand.101" "2" ltac_term:(G)) | idtac "SSR	rand.101	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in b = X); elpi z_report "rand.101" "3" ltac_term:(G)) | idtac "SSR	rand.101	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "rand.101" "4" ltac_term:(G)) | idtac "SSR	rand.101	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _ as X in b = X); elpi z_report "rand.101" "5" ltac_term:(G)) | idtac "SSR	rand.101	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length _ in X in b = X); elpi z_report "rand.101" "6" ltac_term:(G)) | idtac "SSR	rand.101	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b = X); elpi z_report "rand.101" "7" ltac_term:(G)) | idtac "SSR	rand.101	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.101" "8" ltac_term:(G)) | idtac "SSR	rand.101	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.101" "9" ltac_term:(G)) | idtac "SSR	rand.101	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X); elpi z_report "rand.101" "10" ltac_term:(G)) | idtac "SSR	rand.101	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in b = X); elpi z_report "rand.101" "11" ltac_term:(G)) | idtac "SSR	rand.101	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in b = X); elpi z_report "rand.101" "12" ltac_term:(G)) | idtac "SSR	rand.101	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (fst (b, a)) = 
((fst ((g 2), (fst (3, (0 * 0))))) * (length l)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.102" "1" ltac_term:(G)) | idtac "SSR	rand.102	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g 2, fst (3, 0 * 0)) * X); elpi z_report "rand.102" "2" ltac_term:(G)) | idtac "SSR	rand.102	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l as X in fst (b, a) = fst (g 2, fst (3, 0 * 0)) * X); elpi z_report "rand.102" "3" ltac_term:(G)) | idtac "SSR	rand.102	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g 2, fst (3, 0 * 0)) * X); elpi z_report "rand.102" "4" ltac_term:(G)) | idtac "SSR	rand.102	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.102" "5" ltac_term:(G)) | idtac "SSR	rand.102	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in fst (b, a) = fst (g 2, fst (3, _ * 0)) * X); elpi z_report "rand.102" "6" ltac_term:(G)) | idtac "SSR	rand.102	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.102" "7" ltac_term:(G)) | idtac "SSR	rand.102	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.102" "8" ltac_term:(G)) | idtac "SSR	rand.102	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in fst (g 2, fst (3, 0 * 0)) * X); elpi z_report "rand.102" "9" ltac_term:(G)) | idtac "SSR	rand.102	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.102" "10" ltac_term:(G)) | idtac "SSR	rand.102	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in fst (g 2, fst (3, 0 * 0)) * X); elpi z_report "rand.102" "11" ltac_term:(G)) | idtac "SSR	rand.102	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g 2, fst (3, 0 * 0)) * X); elpi z_report "rand.102" "12" ltac_term:(G)) | idtac "SSR	rand.102	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (c, (snd (3, ((f 2 c) * (g c)))))) = 
(f (((length l) + (1 * 3)) + 3) (f c (g (fst (a, 2))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in 1 * X); elpi z_report "rand.103" "1" ltac_term:(G)) | idtac "SSR	rand.103	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l + 1 * S (S X) + 3); elpi z_report "rand.103" "2" ltac_term:(G)) | idtac "SSR	rand.103	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.103" "3" ltac_term:(G)) | idtac "SSR	rand.103	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (c, snd (S (S (S _)), f 2 c * g c)) = f (length l + X * 3 + 3) (f c (g (fst (a, 2))))); elpi z_report "rand.103" "4" ltac_term:(G)) | idtac "SSR	rand.103	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in X * 3); elpi z_report "rand.103" "5" ltac_term:(G)) | idtac "SSR	rand.103	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.103" "6" ltac_term:(G)) | idtac "SSR	rand.103	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (c, snd (3, f 2 c * g c)) = f (length l + X * 3 + 3) (f _ (g (fst (a, 2))))); elpi z_report "rand.103" "7" ltac_term:(G)) | idtac "SSR	rand.103	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f (length l + 1 * 3 + 3) (f _ (g (fst (a, S X))))); elpi z_report "rand.103" "8" ltac_term:(G)) | idtac "SSR	rand.103	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in fst (_, snd (3, f (S X) _ * _)) = f (length _ + 1 * 3 + 3) (f _ (g (fst (a, 2))))); elpi z_report "rand.103" "9" ltac_term:(G)) | idtac "SSR	rand.103	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.103" "10" ltac_term:(G)) | idtac "SSR	rand.103	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X * 3); elpi z_report "rand.103" "11" ltac_term:(G)) | idtac "SSR	rand.103	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length l + 1 * 3 + X); elpi z_report "rand.103" "12" ltac_term:(G)) | idtac "SSR	rand.103	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(3 * (g (snd ((fst (2, b)), (fst (2, b)))))) = 
(f ((length (l ++ l)) * c) (fst (0, ((fst (1, 0)) + 2)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in snd (fst (2, b), fst X)); elpi z_report "rand.104" "1" ltac_term:(G)) | idtac "SSR	rand.104	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (1, 0) + S X); elpi z_report "rand.104" "2" ltac_term:(G)) | idtac "SSR	rand.104	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.104" "3" ltac_term:(G)) | idtac "SSR	rand.104	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in (X, _)); elpi z_report "rand.104" "4" ltac_term:(G)) | idtac "SSR	rand.104	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (_, fst (1, 0) + S X)); elpi z_report "rand.104" "5" ltac_term:(G)) | idtac "SSR	rand.104	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in f (length (l ++ l) * c) (fst (_, fst (_, _) + S X))); elpi z_report "rand.104" "6" ltac_term:(G)) | idtac "SSR	rand.104	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in S (S X) * g (snd (fst (2, b), fst (2, b)))); elpi z_report "rand.104" "7" ltac_term:(G)) | idtac "SSR	rand.104	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (X, 0)); elpi z_report "rand.104" "8" ltac_term:(G)) | idtac "SSR	rand.104	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X) * g (snd (fst (2, b), fst (2, b)))); elpi z_report "rand.104" "9" ltac_term:(G)) | idtac "SSR	rand.104	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.104" "10" ltac_term:(G)) | idtac "SSR	rand.104	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (length (l ++ l) * c) (fst (_, fst (X, 0) + 2))); elpi z_report "rand.104" "11" ltac_term:(G)) | idtac "SSR	rand.104	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (fst (2, b), fst (X, b))); elpi z_report "rand.104" "12" ltac_term:(G)) | idtac "SSR	rand.104	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (fst ((2 * (g 2)), c)) = 
(snd ((f (fst ((length l), (snd (0, a)))) (g (f 3 b))), (((c + 1) * (c + a)) * (f (f 2 c) (length l))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _ in X in fst (2 * g 2, c) = snd (f (fst X) (g (f 3 b)), (_ + 1) * (c + a) * f (f 2 c) (length l))); elpi z_report "rand.105" "1" ltac_term:(G)) | idtac "SSR	rand.105	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (c + 1) * (c + _) * f (f 2 c) X); elpi z_report "rand.105" "2" ltac_term:(G)) | idtac "SSR	rand.105	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f 2 c) X); elpi z_report "rand.105" "3" ltac_term:(G)) | idtac "SSR	rand.105	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.105" "4" ltac_term:(G)) | idtac "SSR	rand.105	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.105" "5" ltac_term:(G)) | idtac "SSR	rand.105	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l in X in (c + 1) * (c + a) * X); elpi z_report "rand.105" "6" ltac_term:(G)) | idtac "SSR	rand.105	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in (X, snd (0, a))); elpi z_report "rand.105" "7" ltac_term:(G)) | idtac "SSR	rand.105	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in (c + 1) * (c + a) * X); elpi z_report "rand.105" "8" ltac_term:(G)) | idtac "SSR	rand.105	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.105" "9" ltac_term:(G)) | idtac "SSR	rand.105	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in (X, snd (0, a))); elpi z_report "rand.105" "10" ltac_term:(G)) | idtac "SSR	rand.105	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in fst (X, snd (0, a))); elpi z_report "rand.105" "11" ltac_term:(G)) | idtac "SSR	rand.105	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in fst (2 * g 2, c) = snd X); elpi z_report "rand.105" "12" ltac_term:(G)) | idtac "SSR	rand.105	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 2 = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.106" "1" ltac_term:(G)) | idtac "SSR	rand.106	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.106" "2" ltac_term:(G)) | idtac "SSR	rand.106	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S X = _); elpi z_report "rand.106" "3" ltac_term:(G)) | idtac "SSR	rand.106	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.106" "4" ltac_term:(G)) | idtac "SSR	rand.106	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X = _); elpi z_report "rand.106" "5" ltac_term:(G)) | idtac "SSR	rand.106	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.106" "6" ltac_term:(G)) | idtac "SSR	rand.106	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in S X); elpi z_report "rand.106" "7" ltac_term:(G)) | idtac "SSR	rand.106	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.106" "8" ltac_term:(G)) | idtac "SSR	rand.106	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.106" "9" ltac_term:(G)) | idtac "SSR	rand.106	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.106" "10" ltac_term:(G)) | idtac "SSR	rand.106	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.106" "11" ltac_term:(G)) | idtac "SSR	rand.106	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.106" "12" ltac_term:(G)) | idtac "SSR	rand.106	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((g (snd (a, b))) + ((fst ((f 1 1), c)) * 3)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (f X 1, _)); elpi z_report "rand.107" "1" ltac_term:(G)) | idtac "SSR	rand.107	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in (f X 1, _)); elpi z_report "rand.107" "2" ltac_term:(G)) | idtac "SSR	rand.107	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l = g (snd (a, b)) + fst (f 1 X, _) * S (S _)); elpi z_report "rand.107" "3" ltac_term:(G)) | idtac "SSR	rand.107	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length l = g (snd (a, b)) + fst (f 1 1, c) * X); elpi z_report "rand.107" "4" ltac_term:(G)) | idtac "SSR	rand.107	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in f 1 X); elpi z_report "rand.107" "5" ltac_term:(G)) | idtac "SSR	rand.107	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (X, _)); elpi z_report "rand.107" "6" ltac_term:(G)) | idtac "SSR	rand.107	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g (snd (a, b)) + X); elpi z_report "rand.107" "7" ltac_term:(G)) | idtac "SSR	rand.107	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in S (S X)); elpi z_report "rand.107" "8" ltac_term:(G)) | idtac "SSR	rand.107	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.107" "9" ltac_term:(G)) | idtac "SSR	rand.107	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.107" "10" ltac_term:(G)) | idtac "SSR	rand.107	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f X 1); elpi z_report "rand.107" "11" ltac_term:(G)) | idtac "SSR	rand.107	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f X 1, _)); elpi z_report "rand.107" "12" ltac_term:(G)) | idtac "SSR	rand.107	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (b, (length ((l ++ l) ++ (1 :: l))))) = (g (fst (a, 0))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, length ((l ++ _) ++ 1 :: l)) = g (fst X)); elpi z_report "rand.108" "1" ltac_term:(G)) | idtac "SSR	rand.108	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, _) in X in fst X); elpi z_report "rand.108" "2" ltac_term:(G)) | idtac "SSR	rand.108	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a, 0); elpi z_report "rand.108" "3" ltac_term:(G)) | idtac "SSR	rand.108	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (b, length ((l ++ l) ++ 1 :: l)) = g (fst X)); elpi z_report "rand.108" "4" ltac_term:(G)) | idtac "SSR	rand.108	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((a, 0) as X in snd (b, length ((l ++ l) ++ 1 :: l)) = g (fst X)); elpi z_report "rand.108" "5" ltac_term:(G)) | idtac "SSR	rand.108	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((_, _) as X in snd (b, length ((l ++ l) ++ 1 :: l)) = g (fst X)); elpi z_report "rand.108" "6" ltac_term:(G)) | idtac "SSR	rand.108	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, 0) in X in snd (b, length ((l ++ l) ++ 1 :: l)) = g X); elpi z_report "rand.108" "7" ltac_term:(G)) | idtac "SSR	rand.108	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, 0) as X in snd (b, length ((l ++ l) ++ 1 :: l)) = g (fst X)); elpi z_report "rand.108" "8" ltac_term:(G)) | idtac "SSR	rand.108	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (fst X)); elpi z_report "rand.108" "9" ltac_term:(G)) | idtac "SSR	rand.108	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (b, length ((l ++ l) ++ 1 :: l)) = g (fst X)); elpi z_report "rand.108" "10" ltac_term:(G)) | idtac "SSR	rand.108	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (b, length ((l ++ l) ++ 1 :: l)) = g (fst X)); elpi z_report "rand.108" "11" ltac_term:(G)) | idtac "SSR	rand.108	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, 0) as X in fst X); elpi z_report "rand.108" "12" ltac_term:(G)) | idtac "SSR	rand.108	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g (g 2)) = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in g (g (S X))); elpi z_report "rand.109" "1" ltac_term:(G)) | idtac "SSR	rand.109	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (g (S X)) = _); elpi z_report "rand.109" "2" ltac_term:(G)) | idtac "SSR	rand.109	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (g (S X)) = b); elpi z_report "rand.109" "3" ltac_term:(G)) | idtac "SSR	rand.109	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g X); elpi z_report "rand.109" "4" ltac_term:(G)) | idtac "SSR	rand.109	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S X)); elpi z_report "rand.109" "5" ltac_term:(G)) | idtac "SSR	rand.109	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X); elpi z_report "rand.109" "6" ltac_term:(G)) | idtac "SSR	rand.109	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S X)); elpi z_report "rand.109" "7" ltac_term:(G)) | idtac "SSR	rand.109	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.109" "8" ltac_term:(G)) | idtac "SSR	rand.109	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (g (S X))); elpi z_report "rand.109" "9" ltac_term:(G)) | idtac "SSR	rand.109	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.109" "10" ltac_term:(G)) | idtac "SSR	rand.109	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.109" "11" ltac_term:(G)) | idtac "SSR	rand.109	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.109" "12" ltac_term:(G)) | idtac "SSR	rand.109	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f c (g (a + b))) * (snd ((f 1 (a * a)), (g (fst (0, c)))))) = 
(f (f ((c + b) + (g b)) (f (b + 3) (0 + b))) (fst ((f (f 0 c) (f 3 c)), (g 1)))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (f (f 0 c) (f 3 c), g X)); elpi z_report "rand.110" "1" ltac_term:(G)) | idtac "SSR	rand.110	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.110" "2" ltac_term:(G)) | idtac "SSR	rand.110	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.110" "3" ltac_term:(G)) | idtac "SSR	rand.110	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in S X); elpi z_report "rand.110" "4" ltac_term:(G)) | idtac "SSR	rand.110	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (f (f 0 c) (f 3 c), X)); elpi z_report "rand.110" "5" ltac_term:(G)) | idtac "SSR	rand.110	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.110" "6" ltac_term:(G)) | idtac "SSR	rand.110	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in (f (f _ _) (f (S X) c), g 1)); elpi z_report "rand.110" "7" ltac_term:(G)) | idtac "SSR	rand.110	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.110" "8" ltac_term:(G)) | idtac "SSR	rand.110	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (f X (a * a), g (fst (0, c)))); elpi z_report "rand.110" "9" ltac_term:(G)) | idtac "SSR	rand.110	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g X); elpi z_report "rand.110" "10" ltac_term:(G)) | idtac "SSR	rand.110	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (f (f _ c) (f 3 _), g X)); elpi z_report "rand.110" "11" ltac_term:(G)) | idtac "SSR	rand.110	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in f c (g (a + b)) * snd (f X (a * _), g (fst (0, c))) = f (f (c + b + g b) (f (b + 3) (0 + b))) (fst (f (f 0 c) (f 3 c), g 1))); elpi z_report "rand.110" "12" ltac_term:(G)) | idtac "SSR	rand.110	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in S X); elpi z_report "rand.111" "1" ltac_term:(G)) | idtac "SSR	rand.111	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.111" "2" ltac_term:(G)) | idtac "SSR	rand.111	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.111" "3" ltac_term:(G)) | idtac "SSR	rand.111	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.111" "4" ltac_term:(G)) | idtac "SSR	rand.111	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.111" "5" ltac_term:(G)) | idtac "SSR	rand.111	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a = S (S X)); elpi z_report "rand.111" "6" ltac_term:(G)) | idtac "SSR	rand.111	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.111" "7" ltac_term:(G)) | idtac "SSR	rand.111	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.111" "8" ltac_term:(G)) | idtac "SSR	rand.111	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.111" "9" ltac_term:(G)) | idtac "SSR	rand.111	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.111" "10" ltac_term:(G)) | idtac "SSR	rand.111	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.111" "11" ltac_term:(G)) | idtac "SSR	rand.111	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.111" "12" ltac_term:(G)) | idtac "SSR	rand.111	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(f (snd (1, c)) (g (snd ((length l), a)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (snd (1, c)) (g (snd (X, a)))); elpi z_report "rand.112" "1" ltac_term:(G)) | idtac "SSR	rand.112	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in snd (X, a)); elpi z_report "rand.112" "2" ltac_term:(G)) | idtac "SSR	rand.112	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in snd X); elpi z_report "rand.112" "3" ltac_term:(G)) | idtac "SSR	rand.112	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in snd (X, a)); elpi z_report "rand.112" "4" ltac_term:(G)) | idtac "SSR	rand.112	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in g (snd X)); elpi z_report "rand.112" "5" ltac_term:(G)) | idtac "SSR	rand.112	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in (X, _)); elpi z_report "rand.112" "6" ltac_term:(G)) | idtac "SSR	rand.112	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in (X, a)); elpi z_report "rand.112" "7" ltac_term:(G)) | idtac "SSR	rand.112	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l as X in snd (X, _)); elpi z_report "rand.112" "8" ltac_term:(G)) | idtac "SSR	rand.112	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in f (snd (1, c)) (g (snd (X, a)))); elpi z_report "rand.112" "9" ltac_term:(G)) | idtac "SSR	rand.112	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l as X in (X, a)); elpi z_report "rand.112" "10" ltac_term:(G)) | idtac "SSR	rand.112	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (snd (X, _))); elpi z_report "rand.112" "11" ltac_term:(G)) | idtac "SSR	rand.112	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in _ = f (snd (1, c)) (g (snd (X, _)))); elpi z_report "rand.112" "12" ltac_term:(G)) | idtac "SSR	rand.112	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length ((l ++ (l ++ l)) ++ l)) = 
b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in length X); elpi z_report "rand.113" "1" ltac_term:(G)) | idtac "SSR	rand.113	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in l ++ X); elpi z_report "rand.113" "2" ltac_term:(G)) | idtac "SSR	rand.113	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in _ ++ X); elpi z_report "rand.113" "3" ltac_term:(G)) | idtac "SSR	rand.113	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in length X = _); elpi z_report "rand.113" "4" ltac_term:(G)) | idtac "SSR	rand.113	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ l); elpi z_report "rand.113" "5" ltac_term:(G)) | idtac "SSR	rand.113	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.113" "6" ltac_term:(G)) | idtac "SSR	rand.113	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in length ((l ++ X) ++ _) = b); elpi z_report "rand.113" "7" ltac_term:(G)) | idtac "SSR	rand.113	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in length ((l ++ X) ++ l) = b); elpi z_report "rand.113" "8" ltac_term:(G)) | idtac "SSR	rand.113	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in _ ++ X); elpi z_report "rand.113" "9" ltac_term:(G)) | idtac "SSR	rand.113	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in (l ++ X) ++ l); elpi z_report "rand.113" "10" ltac_term:(G)) | idtac "SSR	rand.113	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.113" "11" ltac_term:(G)) | idtac "SSR	rand.113	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((_ ++ X) ++ _) = b); elpi z_report "rand.113" "12" ltac_term:(G)) | idtac "SSR	rand.113	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (g ((length l) + (snd (b, 3))))) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.114" "1" ltac_term:(G)) | idtac "SSR	rand.114	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.114" "2" ltac_term:(G)) | idtac "SSR	rand.114	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.114" "3" ltac_term:(G)) | idtac "SSR	rand.114	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S (S X)); elpi z_report "rand.114" "4" ltac_term:(G)) | idtac "SSR	rand.114	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (b, S (S X))); elpi z_report "rand.114" "5" ltac_term:(G)) | idtac "SSR	rand.114	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.114" "6" ltac_term:(G)) | idtac "SSR	rand.114	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.114" "7" ltac_term:(G)) | idtac "SSR	rand.114	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.114" "8" ltac_term:(G)) | idtac "SSR	rand.114	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.114" "9" ltac_term:(G)) | idtac "SSR	rand.114	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in g (g (length l + snd (b, 3))) = S (S X)); elpi z_report "rand.114" "10" ltac_term:(G)) | idtac "SSR	rand.114	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.114" "11" ltac_term:(G)) | idtac "SSR	rand.114	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S (S X)); elpi z_report "rand.114" "12" ltac_term:(G)) | idtac "SSR	rand.114	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (1 + (fst (a, c))) = 
(length (((l ++ l) ++ l) ++ ((2 + a) :: (2 :: l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.115" "1" ltac_term:(G)) | idtac "SSR	rand.115	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.115" "2" ltac_term:(G)) | idtac "SSR	rand.115	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X + _); elpi z_report "rand.115" "3" ltac_term:(G)) | idtac "SSR	rand.115	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.115" "4" ltac_term:(G)) | idtac "SSR	rand.115	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.115" "5" ltac_term:(G)) | idtac "SSR	rand.115	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length X); elpi z_report "rand.115" "6" ltac_term:(G)) | idtac "SSR	rand.115	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in 1 + fst (a, c) = length (((l ++ l) ++ l) ++ S X + _ :: 2 :: l)); elpi z_report "rand.115" "7" ltac_term:(G)) | idtac "SSR	rand.115	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X :: _); elpi z_report "rand.115" "8" ltac_term:(G)) | idtac "SSR	rand.115	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.115" "9" ltac_term:(G)) | idtac "SSR	rand.115	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.115" "10" ltac_term:(G)) | idtac "SSR	rand.115	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.115" "11" ltac_term:(G)) | idtac "SSR	rand.115	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in ((l ++ _) ++ _) ++ 2 + _ :: X); elpi z_report "rand.115" "12" ltac_term:(G)) | idtac "SSR	rand.115	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((g (f b (f 0 c))) + (snd ((g (g 0)), (length (a :: l))))) = ((g 0) + b) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in g (f b (f 0 c)) + snd (g X, length (a :: l)) = g 0 + b); elpi z_report "rand.116" "1" ltac_term:(G)) | idtac "SSR	rand.116	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in g X); elpi z_report "rand.116" "2" ltac_term:(G)) | idtac "SSR	rand.116	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.116" "3" ltac_term:(G)) | idtac "SSR	rand.116	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (g X, length (a :: l))); elpi z_report "rand.116" "4" ltac_term:(G)) | idtac "SSR	rand.116	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0); elpi z_report "rand.116" "5" ltac_term:(G)) | idtac "SSR	rand.116	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in g (f _ (f 0 c)) + snd (g (g 0), length (a :: l)) = X + _); elpi z_report "rand.116" "6" ltac_term:(G)) | idtac "SSR	rand.116	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (f b (f 0 c)) + snd (g X, length (a :: l)) = g 0 + b); elpi z_report "rand.116" "7" ltac_term:(G)) | idtac "SSR	rand.116	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (f b (f 0 c)) + snd (g X, length (a :: l))); elpi z_report "rand.116" "8" ltac_term:(G)) | idtac "SSR	rand.116	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in g X); elpi z_report "rand.116" "9" ltac_term:(G)) | idtac "SSR	rand.116	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g X); elpi z_report "rand.116" "10" ltac_term:(G)) | idtac "SSR	rand.116	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 in X in g (f b (f 0 c)) + snd (X, length (a :: _))); elpi z_report "rand.116" "11" ltac_term:(G)) | idtac "SSR	rand.116	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0); elpi z_report "rand.116" "12" ltac_term:(G)) | idtac "SSR	rand.116	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.117" "1" ltac_term:(G)) | idtac "SSR	rand.117	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.117" "2" ltac_term:(G)) | idtac "SSR	rand.117	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in S X); elpi z_report "rand.117" "3" ltac_term:(G)) | idtac "SSR	rand.117	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.117" "4" ltac_term:(G)) | idtac "SSR	rand.117	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.117" "5" ltac_term:(G)) | idtac "SSR	rand.117	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in length l = S X); elpi z_report "rand.117" "6" ltac_term:(G)) | idtac "SSR	rand.117	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.117" "7" ltac_term:(G)) | idtac "SSR	rand.117	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.117" "8" ltac_term:(G)) | idtac "SSR	rand.117	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length l = X); elpi z_report "rand.117" "9" ltac_term:(G)) | idtac "SSR	rand.117	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.117" "10" ltac_term:(G)) | idtac "SSR	rand.117	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X); elpi z_report "rand.117" "11" ltac_term:(G)) | idtac "SSR	rand.117	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.117" "12" ltac_term:(G)) | idtac "SSR	rand.117	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((snd ((length (a :: l)), (f (snd (1, c)) (b + 1)))) * 3) = 
((f (g (length l)) (g (g c))) * (fst (a, 2))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in snd (length _, f (snd (1, c)) (b + 1)) * 3 = f (g (length l)) (g (g c)) * fst (_, S X)); elpi z_report "rand.118" "1" ltac_term:(G)) | idtac "SSR	rand.118	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (a, S X)); elpi z_report "rand.118" "2" ltac_term:(G)) | idtac "SSR	rand.118	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.118" "3" ltac_term:(G)) | idtac "SSR	rand.118	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (length (a :: l), f (snd (1, c)) (b + 1)) * S (S X) = f (g (length l)) (g (g c)) * fst (a, 2)); elpi z_report "rand.118" "4" ltac_term:(G)) | idtac "SSR	rand.118	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in snd (length (a :: l), f (snd (1, c)) (b + 1)) * S (S X) = f (g (length l)) (g (g c)) * fst (a, 2)); elpi z_report "rand.118" "5" ltac_term:(G)) | idtac "SSR	rand.118	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in snd (length (a :: l), f (snd (1, c)) (b + 1)) * S (S X)); elpi z_report "rand.118" "6" ltac_term:(G)) | idtac "SSR	rand.118	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.118" "7" ltac_term:(G)) | idtac "SSR	rand.118	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in f (g (length l)) (g (g c)) * fst (_, S X)); elpi z_report "rand.118" "8" ltac_term:(G)) | idtac "SSR	rand.118	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (length (a :: l), f (snd (1, c)) (b + 1)) * S (S X) = f (g (length l)) (g (g c)) * fst (a, 2)); elpi z_report "rand.118" "9" ltac_term:(G)) | idtac "SSR	rand.118	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.118" "10" ltac_term:(G)) | idtac "SSR	rand.118	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (_, S X)); elpi z_report "rand.118" "11" ltac_term:(G)) | idtac "SSR	rand.118	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.118" "12" ltac_term:(G)) | idtac "SSR	rand.118	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = a .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.119" "1" ltac_term:(G)) | idtac "SSR	rand.119	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.119" "2" ltac_term:(G)) | idtac "SSR	rand.119	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.119" "3" ltac_term:(G)) | idtac "SSR	rand.119	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.119" "4" ltac_term:(G)) | idtac "SSR	rand.119	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = _); elpi z_report "rand.119" "5" ltac_term:(G)) | idtac "SSR	rand.119	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = _); elpi z_report "rand.119" "6" ltac_term:(G)) | idtac "SSR	rand.119	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = a); elpi z_report "rand.119" "7" ltac_term:(G)) | idtac "SSR	rand.119	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = a); elpi z_report "rand.119" "8" ltac_term:(G)) | idtac "SSR	rand.119	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "rand.119" "9" ltac_term:(G)) | idtac "SSR	rand.119	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ = a); elpi z_report "rand.119" "10" ltac_term:(G)) | idtac "SSR	rand.119	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b = a); elpi z_report "rand.119" "11" ltac_term:(G)) | idtac "SSR	rand.119	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b = _); elpi z_report "rand.119" "12" ltac_term:(G)) | idtac "SSR	rand.119	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((snd ((f c 1), ((length l) * (f 2 0)))) * a) = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in (f c X, _ * f 2 0)); elpi z_report "rand.120" "1" ltac_term:(G)) | idtac "SSR	rand.120	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.120" "2" ltac_term:(G)) | idtac "SSR	rand.120	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (f _ X, length l * f 2 0) * _); elpi z_report "rand.120" "3" ltac_term:(G)) | idtac "SSR	rand.120	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.120" "4" ltac_term:(G)) | idtac "SSR	rand.120	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (f _ X, length l * f 2 0) * a = _); elpi z_report "rand.120" "5" ltac_term:(G)) | idtac "SSR	rand.120	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (f _ 1, X)); elpi z_report "rand.120" "6" ltac_term:(G)) | idtac "SSR	rand.120	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f (S X) 0); elpi z_report "rand.120" "7" ltac_term:(G)) | idtac "SSR	rand.120	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.120" "8" ltac_term:(G)) | idtac "SSR	rand.120	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in snd (f _ X, length l * f 2 _) * a = b); elpi z_report "rand.120" "9" ltac_term:(G)) | idtac "SSR	rand.120	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (f _ X, length l * f 2 0)); elpi z_report "rand.120" "10" ltac_term:(G)) | idtac "SSR	rand.120	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.120" "11" ltac_term:(G)) | idtac "SSR	rand.120	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in snd (f _ X, length l * f 2 0)); elpi z_report "rand.120" "12" ltac_term:(G)) | idtac "SSR	rand.120	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((snd (c, 0)), (g (length l)))) = a .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in (snd (c, 0), g X)); elpi z_report "rand.121" "1" ltac_term:(G)) | idtac "SSR	rand.121	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in (snd (c, 0), g X)); elpi z_report "rand.121" "2" ltac_term:(G)) | idtac "SSR	rand.121	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g X); elpi z_report "rand.121" "3" ltac_term:(G)) | idtac "SSR	rand.121	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in X = _); elpi z_report "rand.121" "4" ltac_term:(G)) | idtac "SSR	rand.121	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length l); elpi z_report "rand.121" "5" ltac_term:(G)) | idtac "SSR	rand.121	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in X = _); elpi z_report "rand.121" "6" ltac_term:(G)) | idtac "SSR	rand.121	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (snd (c, 0), g X)); elpi z_report "rand.121" "7" ltac_term:(G)) | idtac "SSR	rand.121	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length l as X in (snd (c, 0), g X)); elpi z_report "rand.121" "8" ltac_term:(G)) | idtac "SSR	rand.121	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in (snd (c, 0), g X)); elpi z_report "rand.121" "9" ltac_term:(G)) | idtac "SSR	rand.121	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in fst (snd (c, 0), X) = _); elpi z_report "rand.121" "10" ltac_term:(G)) | idtac "SSR	rand.121	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in fst (snd (c, 0), g X) = a); elpi z_report "rand.121" "11" ltac_term:(G)) | idtac "SSR	rand.121	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.121" "12" ltac_term:(G)) | idtac "SSR	rand.121	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g 1) = 
(length (l ++ ((b :: l) ++ (a :: l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in _ ++ X); elpi z_report "rand.122" "1" ltac_term:(G)) | idtac "SSR	rand.122	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _ as X in _ ++ (b :: l) ++ X); elpi z_report "rand.122" "2" ltac_term:(G)) | idtac "SSR	rand.122	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l as X in _ ++ _ ++ X); elpi z_report "rand.122" "3" ltac_term:(G)) | idtac "SSR	rand.122	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _ in X in _ ++ X); elpi z_report "rand.122" "4" ltac_term:(G)) | idtac "SSR	rand.122	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: l as X in g 1 = length (l ++ _ ++ X)); elpi z_report "rand.122" "5" ltac_term:(G)) | idtac "SSR	rand.122	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ :: _ as X in length (l ++ (_ :: _) ++ X)); elpi z_report "rand.122" "6" ltac_term:(G)) | idtac "SSR	rand.122	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g 1 = length (l ++ (_ :: l) ++ X)); elpi z_report "rand.122" "7" ltac_term:(G)) | idtac "SSR	rand.122	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in g 1 = length X); elpi z_report "rand.122" "8" ltac_term:(G)) | idtac "SSR	rand.122	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in g _ = X); elpi z_report "rand.122" "9" ltac_term:(G)) | idtac "SSR	rand.122	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (l ++ (_ :: _) ++ X)); elpi z_report "rand.122" "10" ltac_term:(G)) | idtac "SSR	rand.122	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _ in X in (b :: l) ++ X); elpi z_report "rand.122" "11" ltac_term:(G)) | idtac "SSR	rand.122	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (_ ++ (_ :: l) ++ X)); elpi z_report "rand.122" "12" ltac_term:(G)) | idtac "SSR	rand.122	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
((snd ((1 * (2 * c)), (length (l ++ l)))) + (f c (length (a :: l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ :: _); elpi z_report "rand.123" "1" ltac_term:(G)) | idtac "SSR	rand.123	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: l); elpi z_report "rand.123" "2" ltac_term:(G)) | idtac "SSR	rand.123	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _ in X in length X); elpi z_report "rand.123" "3" ltac_term:(G)) | idtac "SSR	rand.123	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ :: l as X in f _ (length X)); elpi z_report "rand.123" "4" ltac_term:(G)) | idtac "SSR	rand.123	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ :: l); elpi z_report "rand.123" "5" ltac_term:(G)) | idtac "SSR	rand.123	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in length X); elpi z_report "rand.123" "6" ltac_term:(G)) | idtac "SSR	rand.123	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in f _ X); elpi z_report "rand.123" "7" ltac_term:(G)) | idtac "SSR	rand.123	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ :: l); elpi z_report "rand.123" "8" ltac_term:(G)) | idtac "SSR	rand.123	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ as X in snd (1 * (2 * c), length (l ++ l)) + f c (length X)); elpi z_report "rand.123" "9" ltac_term:(G)) | idtac "SSR	rand.123	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in c = snd (1 * (2 * c), length (l ++ l)) + X); elpi z_report "rand.123" "10" ltac_term:(G)) | idtac "SSR	rand.123	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c = snd (1 * (2 * c), length (_ ++ l)) + f _ (length X)); elpi z_report "rand.123" "11" ltac_term:(G)) | idtac "SSR	rand.123	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: _); elpi z_report "rand.123" "12" ltac_term:(G)) | idtac "SSR	rand.123	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g ((length (c :: l)) + 0)) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.124" "1" ltac_term:(G)) | idtac "SSR	rand.124	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in g (length (c :: l) + _) = S (S X)); elpi z_report "rand.124" "2" ltac_term:(G)) | idtac "SSR	rand.124	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.124" "3" ltac_term:(G)) | idtac "SSR	rand.124	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in g (length (c :: l) + _) = S (S X)); elpi z_report "rand.124" "4" ltac_term:(G)) | idtac "SSR	rand.124	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.124" "5" ltac_term:(G)) | idtac "SSR	rand.124	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S X); elpi z_report "rand.124" "6" ltac_term:(G)) | idtac "SSR	rand.124	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (length (c :: l) + 0) = S (S X)); elpi z_report "rand.124" "7" ltac_term:(G)) | idtac "SSR	rand.124	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.124" "8" ltac_term:(G)) | idtac "SSR	rand.124	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.124" "9" ltac_term:(G)) | idtac "SSR	rand.124	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.124" "10" ltac_term:(G)) | idtac "SSR	rand.124	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.124" "11" ltac_term:(G)) | idtac "SSR	rand.124	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (length (c :: l) + 0) = S (S X)); elpi z_report "rand.124" "12" ltac_term:(G)) | idtac "SSR	rand.124	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((1 + (fst ((a + 0), b))) * (length ((length l) :: (3 :: l)))) = 
((f ((2 + c) * (length l)) (fst ((length l), 1))) + (f (length (2 :: l)) b)) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.125" "1" ltac_term:(G)) | idtac "SSR	rand.125	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X + fst (a + 0, b)); elpi z_report "rand.125" "2" ltac_term:(G)) | idtac "SSR	rand.125	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in X + fst (a + 0, _)); elpi z_report "rand.125" "3" ltac_term:(G)) | idtac "SSR	rand.125	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.125" "4" ltac_term:(G)) | idtac "SSR	rand.125	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in S X); elpi z_report "rand.125" "5" ltac_term:(G)) | idtac "SSR	rand.125	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (1 + fst (a + 0, b)) * length (length l :: 3 :: l) = f ((2 + _) * length l) (fst (length l, X)) + f (length (2 :: l)) b); elpi z_report "rand.125" "6" ltac_term:(G)) | idtac "SSR	rand.125	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f ((2 + c) * length l) (fst X) + f (length (2 :: l)) b); elpi z_report "rand.125" "7" ltac_term:(G)) | idtac "SSR	rand.125	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.125" "8" ltac_term:(G)) | idtac "SSR	rand.125	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + c); elpi z_report "rand.125" "9" ltac_term:(G)) | idtac "SSR	rand.125	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length l :: X); elpi z_report "rand.125" "10" ltac_term:(G)) | idtac "SSR	rand.125	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.125" "11" ltac_term:(G)) | idtac "SSR	rand.125	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.125" "12" ltac_term:(G)) | idtac "SSR	rand.125	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((f 2 3) * (snd (c, b))), a)) = (f (length (c :: (a :: l))) a) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f 2 3 * snd (c, b), a) = f (length (c :: X)) _); elpi z_report "rand.126" "1" ltac_term:(G)) | idtac "SSR	rand.126	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in f (length X) _); elpi z_report "rand.126" "2" ltac_term:(G)) | idtac "SSR	rand.126	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l); elpi z_report "rand.126" "3" ltac_term:(G)) | idtac "SSR	rand.126	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: l); elpi z_report "rand.126" "4" ltac_term:(G)) | idtac "SSR	rand.126	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a :: l in X in f X _); elpi z_report "rand.126" "5" ltac_term:(G)) | idtac "SSR	rand.126	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a :: l as X in f (length (_ :: X)) _); elpi z_report "rand.126" "6" ltac_term:(G)) | idtac "SSR	rand.126	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f 2 3 * snd (c, b), a) = f (length (c :: X)) a); elpi z_report "rand.126" "7" ltac_term:(G)) | idtac "SSR	rand.126	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a :: l as X in length (_ :: X)); elpi z_report "rand.126" "8" ltac_term:(G)) | idtac "SSR	rand.126	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in fst (f 2 3 * snd (c, b), a) = f X _); elpi z_report "rand.126" "9" ltac_term:(G)) | idtac "SSR	rand.126	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ :: _ as X in c :: X); elpi z_report "rand.126" "10" ltac_term:(G)) | idtac "SSR	rand.126	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a :: l as X in _ :: X); elpi z_report "rand.126" "11" ltac_term:(G)) | idtac "SSR	rand.126	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a :: l); elpi z_report "rand.126" "12" ltac_term:(G)) | idtac "SSR	rand.126	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (length ((c :: l) ++ l)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (X ++ _)); elpi z_report "rand.127" "1" ltac_term:(G)) | idtac "SSR	rand.127	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c :: l); elpi z_report "rand.127" "2" ltac_term:(G)) | idtac "SSR	rand.127	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X ++ l); elpi z_report "rand.127" "3" ltac_term:(G)) | idtac "SSR	rand.127	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ :: l as X in length (X ++ _)); elpi z_report "rand.127" "4" ltac_term:(G)) | idtac "SSR	rand.127	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length (X ++ _)); elpi z_report "rand.127" "5" ltac_term:(G)) | idtac "SSR	rand.127	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l); elpi z_report "rand.127" "6" ltac_term:(G)) | idtac "SSR	rand.127	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(c :: l in X in X ++ _); elpi z_report "rand.127" "7" ltac_term:(G)) | idtac "SSR	rand.127	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c :: l); elpi z_report "rand.127" "8" ltac_term:(G)) | idtac "SSR	rand.127	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c :: _ in X in X ++ _); elpi z_report "rand.127" "9" ltac_term:(G)) | idtac "SSR	rand.127	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: l in X in 0 = length X); elpi z_report "rand.127" "10" ltac_term:(G)) | idtac "SSR	rand.127	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ :: _ in X in _ = X); elpi z_report "rand.127" "11" ltac_term:(G)) | idtac "SSR	rand.127	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in length (X ++ l)); elpi z_report "rand.127" "12" ltac_term:(G)) | idtac "SSR	rand.127	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (1 * c) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in X * _); elpi z_report "rand.128" "1" ltac_term:(G)) | idtac "SSR	rand.128	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in _ = X * c); elpi z_report "rand.128" "2" ltac_term:(G)) | idtac "SSR	rand.128	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X * _); elpi z_report "rand.128" "3" ltac_term:(G)) | idtac "SSR	rand.128	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in 0 = X * c); elpi z_report "rand.128" "4" ltac_term:(G)) | idtac "SSR	rand.128	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.128" "5" ltac_term:(G)) | idtac "SSR	rand.128	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X * c); elpi z_report "rand.128" "6" ltac_term:(G)) | idtac "SSR	rand.128	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in X * _); elpi z_report "rand.128" "7" ltac_term:(G)) | idtac "SSR	rand.128	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = X * c); elpi z_report "rand.128" "8" ltac_term:(G)) | idtac "SSR	rand.128	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in X * c); elpi z_report "rand.128" "9" ltac_term:(G)) | idtac "SSR	rand.128	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in X * c); elpi z_report "rand.128" "10" ltac_term:(G)) | idtac "SSR	rand.128	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ = X * c); elpi z_report "rand.128" "11" ltac_term:(G)) | idtac "SSR	rand.128	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X * c); elpi z_report "rand.128" "12" ltac_term:(G)) | idtac "SSR	rand.128	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((snd ((snd (c, (0 + 3))), (a + 3))), (length l))) = 
((snd (2, b)) + (f (f (f c 0) (length l)) 3)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.129" "1" ltac_term:(G)) | idtac "SSR	rand.129	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in (c, 0 + S X)); elpi z_report "rand.129" "2" ltac_term:(G)) | idtac "SSR	rand.129	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in snd (snd (X, a + 3), length l)); elpi z_report "rand.129" "3" ltac_term:(G)) | idtac "SSR	rand.129	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.129" "4" ltac_term:(G)) | idtac "SSR	rand.129	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.129" "5" ltac_term:(G)) | idtac "SSR	rand.129	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.129" "6" ltac_term:(G)) | idtac "SSR	rand.129	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (snd (c, 0 + S (S X)), a + 3)); elpi z_report "rand.129" "7" ltac_term:(G)) | idtac "SSR	rand.129	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.129" "8" ltac_term:(G)) | idtac "SSR	rand.129	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.129" "9" ltac_term:(G)) | idtac "SSR	rand.129	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (S X, _)); elpi z_report "rand.129" "10" ltac_term:(G)) | idtac "SSR	rand.129	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.129" "11" ltac_term:(G)) | idtac "SSR	rand.129	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (S X, b)); elpi z_report "rand.129" "12" ltac_term:(G)) | idtac "SSR	rand.129	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f 0 ((f (length l) (snd (3, 2))) + b)) = (g a) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f 0 (f (length l) (snd (3, 2)) + b) = X); elpi z_report "rand.130" "1" ltac_term:(G)) | idtac "SSR	rand.130	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a); elpi z_report "rand.130" "2" ltac_term:(G)) | idtac "SSR	rand.130	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in f 0 (f (length l) (snd (3, 2)) + _) = X); elpi z_report "rand.130" "3" ltac_term:(G)) | idtac "SSR	rand.130	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in f 0 (f (length l) (snd (3, 2)) + _) = X); elpi z_report "rand.130" "4" ltac_term:(G)) | idtac "SSR	rand.130	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in f _ (f (length l) (snd (3, 2)) + b) = X); elpi z_report "rand.130" "5" ltac_term:(G)) | idtac "SSR	rand.130	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.130" "6" ltac_term:(G)) | idtac "SSR	rand.130	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in f 0 (f (length l) (snd (3, 2)) + b) = X); elpi z_report "rand.130" "7" ltac_term:(G)) | idtac "SSR	rand.130	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a as X in f _ (f (length l) (snd (3, 2)) + b) = X); elpi z_report "rand.130" "8" ltac_term:(G)) | idtac "SSR	rand.130	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in f 0 (f (length l) (snd (3, 2)) + b) = X); elpi z_report "rand.130" "9" ltac_term:(G)) | idtac "SSR	rand.130	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a as X in f 0 (f (length l) (snd (3, 2)) + b) = X); elpi z_report "rand.130" "10" ltac_term:(G)) | idtac "SSR	rand.130	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a); elpi z_report "rand.130" "11" ltac_term:(G)) | idtac "SSR	rand.130	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g _); elpi z_report "rand.130" "12" ltac_term:(G)) | idtac "SSR	rand.130	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), ((length (l ++ (l ++ l))) + 3) = 
((g (f (fst (a, c)) (fst (1, 3)))) + b) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = g (f (fst (a, c)) (fst (1, 3))) + b); elpi z_report "rand.131" "1" ltac_term:(G)) | idtac "SSR	rand.131	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.131" "2" ltac_term:(G)) | idtac "SSR	rand.131	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f (fst (a, c)) (fst (X, 3))); elpi z_report "rand.131" "3" ltac_term:(G)) | idtac "SSR	rand.131	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.131" "4" ltac_term:(G)) | idtac "SSR	rand.131	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in (X, 3)); elpi z_report "rand.131" "5" ltac_term:(G)) | idtac "SSR	rand.131	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.131" "6" ltac_term:(G)) | idtac "SSR	rand.131	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in length (l ++ l ++ l) + X); elpi z_report "rand.131" "7" ltac_term:(G)) | idtac "SSR	rand.131	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in (X, 3)); elpi z_report "rand.131" "8" ltac_term:(G)) | idtac "SSR	rand.131	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.131" "9" ltac_term:(G)) | idtac "SSR	rand.131	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.131" "10" ltac_term:(G)) | idtac "SSR	rand.131	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (_ ++ l ++ l) + S (S X) = g (f (fst (a, c)) (fst (1, 3))) + b); elpi z_report "rand.131" "11" ltac_term:(G)) | idtac "SSR	rand.131	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.131" "12" ltac_term:(G)) | idtac "SSR	rand.131	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((snd ((snd ((snd (b, 1)), (g c))), (g (f c b)))), (fst (b, ((snd (c, 1)) + (snd (c, 2))))))) 
= 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (b, snd (c, 1) + snd (c, S X))); elpi z_report "rand.132" "1" ltac_term:(G)) | idtac "SSR	rand.132	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (c, X) + snd (c, 2)); elpi z_report "rand.132" "2" ltac_term:(G)) | idtac "SSR	rand.132	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.132" "3" ltac_term:(G)) | idtac "SSR	rand.132	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, X) + snd (_, 2)); elpi z_report "rand.132" "4" ltac_term:(G)) | idtac "SSR	rand.132	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.132" "5" ltac_term:(G)) | idtac "SSR	rand.132	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.132" "6" ltac_term:(G)) | idtac "SSR	rand.132	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (_, S X)); elpi z_report "rand.132" "7" ltac_term:(G)) | idtac "SSR	rand.132	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X)); elpi z_report "rand.132" "8" ltac_term:(G)) | idtac "SSR	rand.132	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in S X); elpi z_report "rand.132" "9" ltac_term:(G)) | idtac "SSR	rand.132	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.132" "10" ltac_term:(G)) | idtac "SSR	rand.132	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.132" "11" ltac_term:(G)) | idtac "SSR	rand.132	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (b, snd (_, X) + snd (c, 2))); elpi z_report "rand.132" "12" ltac_term:(G)) | idtac "SSR	rand.132	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (a, (fst (3, (fst ((fst (b, c)), 1)))))) = 
(f (snd (((1 + c) * b), (f (f 0 a) (snd (b, b))))) (g (g (snd (0, 2))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.133" "1" ltac_term:(G)) | idtac "SSR	rand.133	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (a, fst (S (S X), fst (fst (b, c), 1)))); elpi z_report "rand.133" "2" ltac_term:(G)) | idtac "SSR	rand.133	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.133" "3" ltac_term:(G)) | idtac "SSR	rand.133	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (g (snd (_, S X)))); elpi z_report "rand.133" "4" ltac_term:(G)) | idtac "SSR	rand.133	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (fst (b, c), X)); elpi z_report "rand.133" "5" ltac_term:(G)) | idtac "SSR	rand.133	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in fst (a, fst (3, fst (fst (b, c), X))) = f (snd ((1 + c) * b, f (f 0 a) (snd (b, b)))) (g (g (snd (0, 2))))); elpi z_report "rand.133" "6" ltac_term:(G)) | idtac "SSR	rand.133	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in S X); elpi z_report "rand.133" "7" ltac_term:(G)) | idtac "SSR	rand.133	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in fst (_, fst (3, fst (fst (b, c), X))) = f (snd ((1 + c) * b, f (f 0 a) (snd (b, b)))) (g (g (snd (0, 2))))); elpi z_report "rand.133" "8" ltac_term:(G)) | idtac "SSR	rand.133	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.133" "9" ltac_term:(G)) | idtac "SSR	rand.133	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (0, S X)); elpi z_report "rand.133" "10" ltac_term:(G)) | idtac "SSR	rand.133	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.133" "11" ltac_term:(G)) | idtac "SSR	rand.133	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (_, fst (3, fst (fst (b, c), X))) = f (snd ((1 + c) * b, f (f 0 a) (snd (b, b)))) (g (g (snd (0, 2))))); elpi z_report "rand.133" "12" ltac_term:(G)) | idtac "SSR	rand.133	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = (length l) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.134" "1" ltac_term:(G)) | idtac "SSR	rand.134	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.134" "2" ltac_term:(G)) | idtac "SSR	rand.134	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in _ = X); elpi z_report "rand.134" "3" ltac_term:(G)) | idtac "SSR	rand.134	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in c = X); elpi z_report "rand.134" "4" ltac_term:(G)) | idtac "SSR	rand.134	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in _ = X); elpi z_report "rand.134" "5" ltac_term:(G)) | idtac "SSR	rand.134	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in c = X); elpi z_report "rand.134" "6" ltac_term:(G)) | idtac "SSR	rand.134	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X); elpi z_report "rand.134" "7" ltac_term:(G)) | idtac "SSR	rand.134	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in c = X); elpi z_report "rand.134" "8" ltac_term:(G)) | idtac "SSR	rand.134	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l as X in c = X); elpi z_report "rand.134" "9" ltac_term:(G)) | idtac "SSR	rand.134	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "rand.134" "10" ltac_term:(G)) | idtac "SSR	rand.134	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.134" "11" ltac_term:(G)) | idtac "SSR	rand.134	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.134" "12" ltac_term:(G)) | idtac "SSR	rand.134	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(fst (2, (g (g (snd (3, a)))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (snd (S (S X), a))); elpi z_report "rand.135" "1" ltac_term:(G)) | idtac "SSR	rand.135	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.135" "2" ltac_term:(G)) | idtac "SSR	rand.135	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = fst (S X, g (g (snd (3, a))))); elpi z_report "rand.135" "3" ltac_term:(G)) | idtac "SSR	rand.135	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.135" "4" ltac_term:(G)) | idtac "SSR	rand.135	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.135" "5" ltac_term:(G)) | idtac "SSR	rand.135	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (S X, g (g (snd (3, a))))); elpi z_report "rand.135" "6" ltac_term:(G)) | idtac "SSR	rand.135	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.135" "7" ltac_term:(G)) | idtac "SSR	rand.135	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.135" "8" ltac_term:(G)) | idtac "SSR	rand.135	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (g (snd (S (S X), _)))); elpi z_report "rand.135" "9" ltac_term:(G)) | idtac "SSR	rand.135	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.135" "10" ltac_term:(G)) | idtac "SSR	rand.135	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.135" "11" ltac_term:(G)) | idtac "SSR	rand.135	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.135" "12" ltac_term:(G)) | idtac "SSR	rand.135	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = a .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = a); elpi z_report "rand.136" "1" ltac_term:(G)) | idtac "SSR	rand.136	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b = a); elpi z_report "rand.136" "2" ltac_term:(G)) | idtac "SSR	rand.136	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = a); elpi z_report "rand.136" "3" ltac_term:(G)) | idtac "SSR	rand.136	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ = a); elpi z_report "rand.136" "4" ltac_term:(G)) | idtac "SSR	rand.136	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = _); elpi z_report "rand.136" "5" ltac_term:(G)) | idtac "SSR	rand.136	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ = _); elpi z_report "rand.136" "6" ltac_term:(G)) | idtac "SSR	rand.136	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.136" "7" ltac_term:(G)) | idtac "SSR	rand.136	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = a); elpi z_report "rand.136" "8" ltac_term:(G)) | idtac "SSR	rand.136	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = a); elpi z_report "rand.136" "9" ltac_term:(G)) | idtac "SSR	rand.136	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = _); elpi z_report "rand.136" "10" ltac_term:(G)) | idtac "SSR	rand.136	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = a); elpi z_report "rand.136" "11" ltac_term:(G)) | idtac "SSR	rand.136	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b = a); elpi z_report "rand.136" "12" ltac_term:(G)) | idtac "SSR	rand.136	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (0, ((f (a + 2) (snd (0, a))) * (g (snd (1, 0)))))) = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X); elpi z_report "rand.137" "1" ltac_term:(G)) | idtac "SSR	rand.137	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X); elpi z_report "rand.137" "2" ltac_term:(G)) | idtac "SSR	rand.137	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in snd (0, f (a + 2) (snd (0, a)) * g (snd (1, 0))) = X); elpi z_report "rand.137" "3" ltac_term:(G)) | idtac "SSR	rand.137	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.137" "4" ltac_term:(G)) | idtac "SSR	rand.137	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (0, f (a + 2) (snd (0, a)) * g (snd (1, 0))) = X); elpi z_report "rand.137" "5" ltac_term:(G)) | idtac "SSR	rand.137	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (0, f (a + S X) (snd (0, a)) * g (snd (1, 0)))); elpi z_report "rand.137" "6" ltac_term:(G)) | idtac "SSR	rand.137	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.137" "7" ltac_term:(G)) | idtac "SSR	rand.137	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (0, f (a + 2) (snd (0, a)) * g (snd (1, 0))) = S X); elpi z_report "rand.137" "8" ltac_term:(G)) | idtac "SSR	rand.137	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.137" "9" ltac_term:(G)) | idtac "SSR	rand.137	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in (_, f (a + 2) (snd (_, a)) * g (snd (X, 0)))); elpi z_report "rand.137" "10" ltac_term:(G)) | idtac "SSR	rand.137	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.137" "11" ltac_term:(G)) | idtac "SSR	rand.137	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.137" "12" ltac_term:(G)) | idtac "SSR	rand.137	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f 2 ((length l) * (fst ((a * c), (fst (1, a)))))) = 
(f a (f b (1 + (0 + 1)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.138" "1" ltac_term:(G)) | idtac "SSR	rand.138	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f 2 X = f a (f b (1 + (0 + 1)))); elpi z_report "rand.138" "2" ltac_term:(G)) | idtac "SSR	rand.138	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in S X); elpi z_report "rand.138" "3" ltac_term:(G)) | idtac "SSR	rand.138	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.138" "4" ltac_term:(G)) | idtac "SSR	rand.138	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f 2 (length l * fst (a * c, fst (1, a))) = f _ (f _ (X + (0 + 1)))); elpi z_report "rand.138" "5" ltac_term:(G)) | idtac "SSR	rand.138	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst X); elpi z_report "rand.138" "6" ltac_term:(G)) | idtac "SSR	rand.138	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + X); elpi z_report "rand.138" "7" ltac_term:(G)) | idtac "SSR	rand.138	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in 1 + X); elpi z_report "rand.138" "8" ltac_term:(G)) | idtac "SSR	rand.138	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (X, a)); elpi z_report "rand.138" "9" ltac_term:(G)) | idtac "SSR	rand.138	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f a (f _ X)); elpi z_report "rand.138" "10" ltac_term:(G)) | idtac "SSR	rand.138	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.138" "11" ltac_term:(G)) | idtac "SSR	rand.138	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in f 2 (length l * fst (a * c, fst (X, _))) = f a (f b (1 + (0 + 1)))); elpi z_report "rand.138" "12" ltac_term:(G)) | idtac "SSR	rand.138	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g (g (c * b))) = 
(f (snd (2, ((snd (a, c)) * (f c a)))) ((length (3 :: l)) * ((f 0 3) * (g 1)))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f 0 3 * g X); elpi z_report "rand.139" "1" ltac_term:(G)) | idtac "SSR	rand.139	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.139" "2" ltac_term:(G)) | idtac "SSR	rand.139	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in length (3 :: l) * (f 0 3 * g X)); elpi z_report "rand.139" "3" ltac_term:(G)) | idtac "SSR	rand.139	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (g (c * b)) = f (snd (2, snd (a, c) * f c a)) (length (3 :: l) * (f _ (S (S X)) * g 1))); elpi z_report "rand.139" "4" ltac_term:(G)) | idtac "SSR	rand.139	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in f _ 3 * g X); elpi z_report "rand.139" "5" ltac_term:(G)) | idtac "SSR	rand.139	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.139" "6" ltac_term:(G)) | idtac "SSR	rand.139	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g X); elpi z_report "rand.139" "7" ltac_term:(G)) | idtac "SSR	rand.139	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.139" "8" ltac_term:(G)) | idtac "SSR	rand.139	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.139" "9" ltac_term:(G)) | idtac "SSR	rand.139	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (g (c * b)) = f (snd (2, snd (a, c) * f c a)) (length (S (S X) :: _) * (f 0 3 * g 1))); elpi z_report "rand.139" "10" ltac_term:(G)) | idtac "SSR	rand.139	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f (snd X) (length (3 :: l) * (f 0 3 * g 1))); elpi z_report "rand.139" "11" ltac_term:(G)) | idtac "SSR	rand.139	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in f 0 3 * X); elpi z_report "rand.139" "12" ltac_term:(G)) | idtac "SSR	rand.139	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((g (3 + c)) * (g (f 3 a))) * (fst (3, a))) = 0 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (S (S X), a)); elpi z_report "rand.140" "1" ltac_term:(G)) | idtac "SSR	rand.140	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.140" "2" ltac_term:(G)) | idtac "SSR	rand.140	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.140" "3" ltac_term:(G)) | idtac "SSR	rand.140	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.140" "4" ltac_term:(G)) | idtac "SSR	rand.140	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S (S X) + c) * g (f 3 a) * fst (3, a)); elpi z_report "rand.140" "5" ltac_term:(G)) | idtac "SSR	rand.140	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.140" "6" ltac_term:(G)) | idtac "SSR	rand.140	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g (S X + c) * g (f 3 a)); elpi z_report "rand.140" "7" ltac_term:(G)) | idtac "SSR	rand.140	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.140" "8" ltac_term:(G)) | idtac "SSR	rand.140	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.140" "9" ltac_term:(G)) | idtac "SSR	rand.140	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in S (S X)); elpi z_report "rand.140" "10" ltac_term:(G)) | idtac "SSR	rand.140	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.140" "11" ltac_term:(G)) | idtac "SSR	rand.140	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in g (3 + c) * g (f (S (S X)) a) * fst (3, a) = 0); elpi z_report "rand.140" "12" ltac_term:(G)) | idtac "SSR	rand.140	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (a, (fst (b, (snd (b, 0)))))) 
= (snd (2, 0)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.141" "1" ltac_term:(G)) | idtac "SSR	rand.141	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, fst (b, snd (b, _))) = snd (S X, 0)); elpi z_report "rand.141" "2" ltac_term:(G)) | idtac "SSR	rand.141	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (S X, 0)); elpi z_report "rand.141" "3" ltac_term:(G)) | idtac "SSR	rand.141	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.141" "4" ltac_term:(G)) | idtac "SSR	rand.141	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.141" "5" ltac_term:(G)) | idtac "SSR	rand.141	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.141" "6" ltac_term:(G)) | idtac "SSR	rand.141	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.141" "7" ltac_term:(G)) | idtac "SSR	rand.141	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.141" "8" ltac_term:(G)) | idtac "SSR	rand.141	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (S X, _)); elpi z_report "rand.141" "9" ltac_term:(G)) | idtac "SSR	rand.141	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.141" "10" ltac_term:(G)) | idtac "SSR	rand.141	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.141" "11" ltac_term:(G)) | idtac "SSR	rand.141	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.141" "12" ltac_term:(G)) | idtac "SSR	rand.141	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = 
((snd ((length (l ++ l)), (g a))) * (1 + (snd ((snd (a, a)), (fst (c, b)))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((c, _) as X in (snd (a, _), fst X)); elpi z_report "rand.142" "1" ltac_term:(G)) | idtac "SSR	rand.142	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, b); elpi z_report "rand.142" "2" ltac_term:(G)) | idtac "SSR	rand.142	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c, _); elpi z_report "rand.142" "3" ltac_term:(G)) | idtac "SSR	rand.142	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a = snd (length (l ++ l), g a) * (S _ + snd (snd (a, a), fst X))); elpi z_report "rand.142" "4" ltac_term:(G)) | idtac "SSR	rand.142	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c, _); elpi z_report "rand.142" "5" ltac_term:(G)) | idtac "SSR	rand.142	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_, _); elpi z_report "rand.142" "6" ltac_term:(G)) | idtac "SSR	rand.142	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c, b); elpi z_report "rand.142" "7" ltac_term:(G)) | idtac "SSR	rand.142	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in 1 + snd (snd (a, a), fst X)); elpi z_report "rand.142" "8" ltac_term:(G)) | idtac "SSR	rand.142	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd (length (l ++ l), g _) * (1 + snd (snd (a, a), fst X))); elpi z_report "rand.142" "9" ltac_term:(G)) | idtac "SSR	rand.142	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (snd (a, a), fst X)); elpi z_report "rand.142" "10" ltac_term:(G)) | idtac "SSR	rand.142	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c, _); elpi z_report "rand.142" "11" ltac_term:(G)) | idtac "SSR	rand.142	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (snd (_, a), fst X)); elpi z_report "rand.142" "12" ltac_term:(G)) | idtac "SSR	rand.142	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((fst ((0 * (fst (2, 1))), ((fst (1, 1)) * (fst (2, 3))))), (length ((l ++ l) ++ (a :: l))))) 
= 
((1 * (snd (b, (a + b)))) * (snd ((fst ((2 * c), (snd (c, 0)))), (snd ((1 * 0), 3))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X * _); elpi z_report "rand.143" "1" ltac_term:(G)) | idtac "SSR	rand.143	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.143" "2" ltac_term:(G)) | idtac "SSR	rand.143	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (fst (0 * fst (2, 1), fst (1, 1) * fst (2, 3)), length ((l ++ l) ++ a :: l)) = 1 * snd (_, a + b) * snd (fst (2 * c, snd (c, 0)), snd (X * 0, 3))); elpi z_report "rand.143" "3" ltac_term:(G)) | idtac "SSR	rand.143	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.143" "4" ltac_term:(G)) | idtac "SSR	rand.143	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (2, S (S X))); elpi z_report "rand.143" "5" ltac_term:(G)) | idtac "SSR	rand.143	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.143" "6" ltac_term:(G)) | idtac "SSR	rand.143	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.143" "7" ltac_term:(G)) | idtac "SSR	rand.143	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (fst (2 * c, snd (c, 0)), snd (X * 0, 3))); elpi z_report "rand.143" "8" ltac_term:(G)) | idtac "SSR	rand.143	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (fst (0 * fst (2, 1), fst (1, X) * fst (2, 3)), length ((l ++ l) ++ a :: l))); elpi z_report "rand.143" "9" ltac_term:(G)) | idtac "SSR	rand.143	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (_ * fst (2, 1), fst (1, 1) * fst (2, S (S X)))); elpi z_report "rand.143" "10" ltac_term:(G)) | idtac "SSR	rand.143	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.143" "11" ltac_term:(G)) | idtac "SSR	rand.143	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in (fst (_ * fst (2, 1), fst (X, 1) * fst (2, 3)), length ((l ++ l) ++ a :: l))); elpi z_report "rand.143" "12" ltac_term:(G)) | idtac "SSR	rand.143	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), a = (a * (f b 0)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ 0); elpi z_report "rand.144" "1" ltac_term:(G)) | idtac "SSR	rand.144	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in a * X); elpi z_report "rand.144" "2" ltac_term:(G)) | idtac "SSR	rand.144	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "rand.144" "3" ltac_term:(G)) | idtac "SSR	rand.144	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(f b 0 in X in a * X); elpi z_report "rand.144" "4" ltac_term:(G)) | idtac "SSR	rand.144	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f b 0 in X in _ = X); elpi z_report "rand.144" "5" ltac_term:(G)) | idtac "SSR	rand.144	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f b 0); elpi z_report "rand.144" "6" ltac_term:(G)) | idtac "SSR	rand.144	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a * X); elpi z_report "rand.144" "7" ltac_term:(G)) | idtac "SSR	rand.144	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f b 0 in X in a * X); elpi z_report "rand.144" "8" ltac_term:(G)) | idtac "SSR	rand.144	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ = a * X); elpi z_report "rand.144" "9" ltac_term:(G)) | idtac "SSR	rand.144	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a * X); elpi z_report "rand.144" "10" ltac_term:(G)) | idtac "SSR	rand.144	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(f b 0 as X in a = _ * X); elpi z_report "rand.144" "11" ltac_term:(G)) | idtac "SSR	rand.144	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _ in X in _ = X); elpi z_report "rand.144" "12" ltac_term:(G)) | idtac "SSR	rand.144	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (fst ((g 3), 1)) = 0 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.145" "1" ltac_term:(G)) | idtac "SSR	rand.145	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (g 3, X)); elpi z_report "rand.145" "2" ltac_term:(G)) | idtac "SSR	rand.145	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.145" "3" ltac_term:(G)) | idtac "SSR	rand.145	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.145" "4" ltac_term:(G)) | idtac "SSR	rand.145	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g 3, X)); elpi z_report "rand.145" "5" ltac_term:(G)) | idtac "SSR	rand.145	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X = _); elpi z_report "rand.145" "6" ltac_term:(G)) | idtac "SSR	rand.145	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (g 3, X) = 0); elpi z_report "rand.145" "7" ltac_term:(G)) | idtac "SSR	rand.145	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g 3, X)); elpi z_report "rand.145" "8" ltac_term:(G)) | idtac "SSR	rand.145	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (g (S (S X)), S _)); elpi z_report "rand.145" "9" ltac_term:(G)) | idtac "SSR	rand.145	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S (S X)); elpi z_report "rand.145" "10" ltac_term:(G)) | idtac "SSR	rand.145	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.145" "11" ltac_term:(G)) | idtac "SSR	rand.145	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.145" "12" ltac_term:(G)) | idtac "SSR	rand.145	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((2 + 1) :: (l ++ (2 :: l)))) = 
(f (snd ((snd (a, (fst (a, 3)))), ((f 1 b) * 3))) a) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.146" "1" ltac_term:(G)) | idtac "SSR	rand.146	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.146" "2" ltac_term:(G)) | idtac "SSR	rand.146	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.146" "3" ltac_term:(G)) | idtac "SSR	rand.146	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.146" "4" ltac_term:(G)) | idtac "SSR	rand.146	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in length (2 + X :: l ++ 2 :: l)); elpi z_report "rand.146" "5" ltac_term:(G)) | idtac "SSR	rand.146	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (snd (a, fst (a, 3)), f (S _) _ * S (S X))); elpi z_report "rand.146" "6" ltac_term:(G)) | idtac "SSR	rand.146	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X + S _); elpi z_report "rand.146" "7" ltac_term:(G)) | idtac "SSR	rand.146	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X :: l ++ 2 :: l); elpi z_report "rand.146" "8" ltac_term:(G)) | idtac "SSR	rand.146	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.146" "9" ltac_term:(G)) | idtac "SSR	rand.146	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in f (snd (snd (a, fst (a, 3)), f X _ * 3)) _); elpi z_report "rand.146" "10" ltac_term:(G)) | idtac "SSR	rand.146	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (snd (a, fst (a, 3)), X)); elpi z_report "rand.146" "11" ltac_term:(G)) | idtac "SSR	rand.146	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.146" "12" ltac_term:(G)) | idtac "SSR	rand.146	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 3 = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.147" "1" ltac_term:(G)) | idtac "SSR	rand.147	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.147" "2" ltac_term:(G)) | idtac "SSR	rand.147	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 = S (S X)); elpi z_report "rand.147" "3" ltac_term:(G)) | idtac "SSR	rand.147	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in S X); elpi z_report "rand.147" "4" ltac_term:(G)) | idtac "SSR	rand.147	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.147" "5" ltac_term:(G)) | idtac "SSR	rand.147	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.147" "6" ltac_term:(G)) | idtac "SSR	rand.147	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in 3 = S (S X)); elpi z_report "rand.147" "7" ltac_term:(G)) | idtac "SSR	rand.147	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.147" "8" ltac_term:(G)) | idtac "SSR	rand.147	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.147" "9" ltac_term:(G)) | idtac "SSR	rand.147	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 3 = S (S X)); elpi z_report "rand.147" "10" ltac_term:(G)) | idtac "SSR	rand.147	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) = 3); elpi z_report "rand.147" "11" ltac_term:(G)) | idtac "SSR	rand.147	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.147" "12" ltac_term:(G)) | idtac "SSR	rand.147	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (fst (2, 3)) = 
(fst (((length l) * 2), a)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.148" "1" ltac_term:(G)) | idtac "SSR	rand.148	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (2, S (S X))); elpi z_report "rand.148" "2" ltac_term:(G)) | idtac "SSR	rand.148	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (2, 3) = fst (length _ * S X, a)); elpi z_report "rand.148" "3" ltac_term:(G)) | idtac "SSR	rand.148	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.148" "4" ltac_term:(G)) | idtac "SSR	rand.148	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (2, S (S X))); elpi z_report "rand.148" "5" ltac_term:(G)) | idtac "SSR	rand.148	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (2, S (S X))); elpi z_report "rand.148" "6" ltac_term:(G)) | idtac "SSR	rand.148	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (S X, 3) = fst (length l * 2, a)); elpi z_report "rand.148" "7" ltac_term:(G)) | idtac "SSR	rand.148	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.148" "8" ltac_term:(G)) | idtac "SSR	rand.148	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.148" "9" ltac_term:(G)) | idtac "SSR	rand.148	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in fst (2, 3) = fst (length l * S X, a)); elpi z_report "rand.148" "10" ltac_term:(G)) | idtac "SSR	rand.148	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.148" "11" ltac_term:(G)) | idtac "SSR	rand.148	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (2, S (S X)) = fst (length l * 2, a)); elpi z_report "rand.148" "12" ltac_term:(G)) | idtac "SSR	rand.148	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (a * ((2 * c) + b)) ((length (l ++ l)) + a)) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f (_ * X) (length (l ++ l) + a)); elpi z_report "rand.149" "1" ltac_term:(G)) | idtac "SSR	rand.149	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.149" "2" ltac_term:(G)) | idtac "SSR	rand.149	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.149" "3" ltac_term:(G)) | idtac "SSR	rand.149	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.149" "4" ltac_term:(G)) | idtac "SSR	rand.149	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.149" "5" ltac_term:(G)) | idtac "SSR	rand.149	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.149" "6" ltac_term:(G)) | idtac "SSR	rand.149	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.149" "7" ltac_term:(G)) | idtac "SSR	rand.149	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (a * (2 * c + b)) (length (l ++ l) + a) = S (S X)); elpi z_report "rand.149" "8" ltac_term:(G)) | idtac "SSR	rand.149	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.149" "9" ltac_term:(G)) | idtac "SSR	rand.149	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.149" "10" ltac_term:(G)) | idtac "SSR	rand.149	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X * c); elpi z_report "rand.149" "11" ltac_term:(G)) | idtac "SSR	rand.149	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in a * (X * c + b)); elpi z_report "rand.149" "12" ltac_term:(G)) | idtac "SSR	rand.149	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((fst ((g 1), (length l))) + (g 1)), 3)) = 
((f (3 * 3) 0) * (fst ((snd (2, 2)), 1))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (fst (g X, _) + g 1, S (S _)) = f (3 * 3) 0 * fst (snd (2, 2), 1)); elpi z_report "rand.150" "1" ltac_term:(G)) | idtac "SSR	rand.150	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.150" "2" ltac_term:(G)) | idtac "SSR	rand.150	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.150" "3" ltac_term:(G)) | idtac "SSR	rand.150	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.150" "4" ltac_term:(G)) | idtac "SSR	rand.150	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (3 * 3) 0 * fst (snd (2, S X), 1)); elpi z_report "rand.150" "5" ltac_term:(G)) | idtac "SSR	rand.150	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.150" "6" ltac_term:(G)) | idtac "SSR	rand.150	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X) * 3); elpi z_report "rand.150" "7" ltac_term:(G)) | idtac "SSR	rand.150	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f (3 * X) _ * fst (snd (2, 2), 1)); elpi z_report "rand.150" "8" ltac_term:(G)) | idtac "SSR	rand.150	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (S X, 2)); elpi z_report "rand.150" "9" ltac_term:(G)) | idtac "SSR	rand.150	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in S X); elpi z_report "rand.150" "10" ltac_term:(G)) | idtac "SSR	rand.150	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.150" "11" ltac_term:(G)) | idtac "SSR	rand.150	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.150" "12" ltac_term:(G)) | idtac "SSR	rand.150	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((snd ((length (l ++ l)), (c + (f 1 a)))) + 1) = 
(length (((f b 2) :: (l ++ l)) ++ ((length l) :: (l ++ l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in (X, _ + f 1 _)); elpi z_report "rand.151" "1" ltac_term:(G)) | idtac "SSR	rand.151	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in X ++ length l :: l ++ l); elpi z_report "rand.151" "2" ltac_term:(G)) | idtac "SSR	rand.151	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in length (X ++ length l :: l ++ l)); elpi z_report "rand.151" "3" ltac_term:(G)) | idtac "SSR	rand.151	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in X ++ length l :: l ++ l); elpi z_report "rand.151" "4" ltac_term:(G)) | idtac "SSR	rand.151	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in snd (length (l ++ l), c + f 1 a) + _ = length ((f b 2 :: l ++ l) ++ length l :: X)); elpi z_report "rand.151" "5" ltac_term:(G)) | idtac "SSR	rand.151	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((f b 2 :: l ++ l) ++ length _ :: X)); elpi z_report "rand.151" "6" ltac_term:(G)) | idtac "SSR	rand.151	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.151" "7" ltac_term:(G)) | idtac "SSR	rand.151	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (length (l ++ l), c + f 1 a) + 1 = length ((f b 2 :: X) ++ length l :: l ++ l)); elpi z_report "rand.151" "8" ltac_term:(G)) | idtac "SSR	rand.151	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.151" "9" ltac_term:(G)) | idtac "SSR	rand.151	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (length X, _ + f 1 _) + 1); elpi z_report "rand.151" "10" ltac_term:(G)) | idtac "SSR	rand.151	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((f b 2 :: l ++ l) ++ _ :: X)); elpi z_report "rand.151" "11" ltac_term:(G)) | idtac "SSR	rand.151	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in length ((f b 2 :: l ++ l) ++ length l :: X)); elpi z_report "rand.151" "12" ltac_term:(G)) | idtac "SSR	rand.151	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (snd ((f 3 (g 2)), (snd ((g 3), (snd (a, 3))))))) = 1 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in g X = 1); elpi z_report "rand.152" "1" ltac_term:(G)) | idtac "SSR	rand.152	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in snd X); elpi z_report "rand.152" "2" ltac_term:(G)) | idtac "SSR	rand.152	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.152" "3" ltac_term:(G)) | idtac "SSR	rand.152	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.152" "4" ltac_term:(G)) | idtac "SSR	rand.152	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (f 3 (g 2), snd (g (S (S X)), snd (a, 3)))); elpi z_report "rand.152" "5" ltac_term:(G)) | idtac "SSR	rand.152	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.152" "6" ltac_term:(G)) | idtac "SSR	rand.152	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.152" "7" ltac_term:(G)) | idtac "SSR	rand.152	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in (a, S (S X))); elpi z_report "rand.152" "8" ltac_term:(G)) | idtac "SSR	rand.152	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in (g (S (S X)), snd (a, 3))); elpi z_report "rand.152" "9" ltac_term:(G)) | idtac "SSR	rand.152	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (snd (f 3 (g (S X)), snd (g 3, snd (a, 3)))) = S _); elpi z_report "rand.152" "10" ltac_term:(G)) | idtac "SSR	rand.152	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f X (g 2)); elpi z_report "rand.152" "11" ltac_term:(G)) | idtac "SSR	rand.152	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (snd (f 3 (g 2), snd (g 3, snd (_, S (S X)))))); elpi z_report "rand.152" "12" ltac_term:(G)) | idtac "SSR	rand.152	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g ((length l) + (length (c :: l)))) = (3 * (length (a :: (l ++ l)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in length X); elpi z_report "rand.153" "1" ltac_term:(G)) | idtac "SSR	rand.153	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ _ in X in _ :: X); elpi z_report "rand.153" "2" ltac_term:(G)) | idtac "SSR	rand.153	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ l in X in a :: X); elpi z_report "rand.153" "3" ltac_term:(G)) | idtac "SSR	rand.153	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in 3 * length (a :: X)); elpi z_report "rand.153" "4" ltac_term:(G)) | idtac "SSR	rand.153	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in length (a :: X)); elpi z_report "rand.153" "5" ltac_term:(G)) | idtac "SSR	rand.153	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a :: X); elpi z_report "rand.153" "6" ltac_term:(G)) | idtac "SSR	rand.153	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(l ++ _); elpi z_report "rand.153" "7" ltac_term:(G)) | idtac "SSR	rand.153	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l as X in 3 * length (_ :: X)); elpi z_report "rand.153" "8" ltac_term:(G)) | idtac "SSR	rand.153	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.153" "9" ltac_term:(G)) | idtac "SSR	rand.153	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l as X in g (length l + length (c :: l)) = 3 * length (a :: X)); elpi z_report "rand.153" "10" ltac_term:(G)) | idtac "SSR	rand.153	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ l as X in _ :: X); elpi z_report "rand.153" "11" ltac_term:(G)) | idtac "SSR	rand.153	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.153" "12" ltac_term:(G)) | idtac "SSR	rand.153	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (c, b)) = a .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in snd X = a); elpi z_report "rand.154" "1" ltac_term:(G)) | idtac "SSR	rand.154	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd X); elpi z_report "rand.154" "2" ltac_term:(G)) | idtac "SSR	rand.154	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd X); elpi z_report "rand.154" "3" ltac_term:(G)) | idtac "SSR	rand.154	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd X); elpi z_report "rand.154" "4" ltac_term:(G)) | idtac "SSR	rand.154	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, _) in X in X = a); elpi z_report "rand.154" "5" ltac_term:(G)) | idtac "SSR	rand.154	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, b) as X in snd X); elpi z_report "rand.154" "6" ltac_term:(G)) | idtac "SSR	rand.154	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, b); elpi z_report "rand.154" "7" ltac_term:(G)) | idtac "SSR	rand.154	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}((_, _) as X in snd X); elpi z_report "rand.154" "8" ltac_term:(G)) | idtac "SSR	rand.154	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd X); elpi z_report "rand.154" "9" ltac_term:(G)) | idtac "SSR	rand.154	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}((c, _) in X in snd X); elpi z_report "rand.154" "10" ltac_term:(G)) | idtac "SSR	rand.154	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((_, b) in X in X = _); elpi z_report "rand.154" "11" ltac_term:(G)) | idtac "SSR	rand.154	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((c, _) as X in snd X); elpi z_report "rand.154" "12" ltac_term:(G)) | idtac "SSR	rand.154	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
(fst ((snd (1, (g a))), (((f 0 3) + (snd (a, c))) * (length (l ++ l))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in c = fst (snd (1, g a), X)); elpi z_report "rand.155" "1" ltac_term:(G)) | idtac "SSR	rand.155	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ l as X in (f 0 3 + snd (a, c)) * length X); elpi z_report "rand.155" "2" ltac_term:(G)) | idtac "SSR	rand.155	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.155" "3" ltac_term:(G)) | idtac "SSR	rand.155	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.155" "4" ltac_term:(G)) | idtac "SSR	rand.155	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = fst (snd (1, g a), (f 0 (S (S _)) + snd (a, c)) * length X)); elpi z_report "rand.155" "5" ltac_term:(G)) | idtac "SSR	rand.155	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ _ in X in (snd (1, g a), (f 0 3 + snd (a, c)) * X)); elpi z_report "rand.155" "6" ltac_term:(G)) | idtac "SSR	rand.155	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ ++ l); elpi z_report "rand.155" "7" ltac_term:(G)) | idtac "SSR	rand.155	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ _ as X in (snd (1, g a), (f 0 3 + snd (a, c)) * length X)); elpi z_report "rand.155" "8" ltac_term:(G)) | idtac "SSR	rand.155	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in c = fst (snd (1, g a), (f _ 3 + snd (a, c)) * length X)); elpi z_report "rand.155" "9" ltac_term:(G)) | idtac "SSR	rand.155	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (f 0 3 + snd (a, c)) * length X); elpi z_report "rand.155" "10" ltac_term:(G)) | idtac "SSR	rand.155	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ l in X in (snd (_, g a), (f 0 3 + snd (a, c)) * X)); elpi z_report "rand.155" "11" ltac_term:(G)) | idtac "SSR	rand.155	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.155" "12" ltac_term:(G)) | idtac "SSR	rand.155	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (f (f b a) (f 1 (snd ((g 2), 0)))) 
= ((fst ((g (a + 3)), (g (snd (1, 0))))) * 1) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.156" "1" ltac_term:(G)) | idtac "SSR	rand.156	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (_ + S (S X))); elpi z_report "rand.156" "2" ltac_term:(G)) | idtac "SSR	rand.156	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (g (_ + S (S X)), g (snd (1, 0)))); elpi z_report "rand.156" "3" ltac_term:(G)) | idtac "SSR	rand.156	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.156" "4" ltac_term:(G)) | idtac "SSR	rand.156	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst (g (a + 3), g (snd (1, 0))) * X); elpi z_report "rand.156" "5" ltac_term:(G)) | idtac "SSR	rand.156	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in f (f b a) (f X (snd (g 2, 0))) = fst (g (a + 3), g (snd (1, 0))) * S _); elpi z_report "rand.156" "6" ltac_term:(G)) | idtac "SSR	rand.156	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (f b a) (f 1 (snd (g 2, 0))) = fst (g (a + 3), X) * 1); elpi z_report "rand.156" "7" ltac_term:(G)) | idtac "SSR	rand.156	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (S X)); elpi z_report "rand.156" "8" ltac_term:(G)) | idtac "SSR	rand.156	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f (f b a) (f 1 (snd (g 2, 0))) = fst (g (a + 3), g (snd (1, 0))) * X); elpi z_report "rand.156" "9" ltac_term:(G)) | idtac "SSR	rand.156	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in (g (S X), 0)); elpi z_report "rand.156" "10" ltac_term:(G)) | idtac "SSR	rand.156	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.156" "11" ltac_term:(G)) | idtac "SSR	rand.156	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (f b _) X = fst (g (a + 3), g (snd (1, 0))) * 1); elpi z_report "rand.156" "12" ltac_term:(G)) | idtac "SSR	rand.156	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (f (g (g (c * 0))) c) = 
(f (fst (a, 2)) 3) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in f (fst (_, X)) 3); elpi z_report "rand.157" "1" ltac_term:(G)) | idtac "SSR	rand.157	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in f (g (g (c * 0))) c = f (fst (a, 2)) (S (S X))); elpi z_report "rand.157" "2" ltac_term:(G)) | idtac "SSR	rand.157	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in f (fst (a, 2)) X); elpi z_report "rand.157" "3" ltac_term:(G)) | idtac "SSR	rand.157	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.157" "4" ltac_term:(G)) | idtac "SSR	rand.157	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.157" "5" ltac_term:(G)) | idtac "SSR	rand.157	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.157" "6" ltac_term:(G)) | idtac "SSR	rand.157	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in fst (a, S X)); elpi z_report "rand.157" "7" ltac_term:(G)) | idtac "SSR	rand.157	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in S X); elpi z_report "rand.157" "8" ltac_term:(G)) | idtac "SSR	rand.157	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (g (g (c * 0))) c = f (fst (a, S X)) 3); elpi z_report "rand.157" "9" ltac_term:(G)) | idtac "SSR	rand.157	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (_, X)); elpi z_report "rand.157" "10" ltac_term:(G)) | idtac "SSR	rand.157	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S (S X)); elpi z_report "rand.157" "11" ltac_term:(G)) | idtac "SSR	rand.157	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.157" "12" ltac_term:(G)) | idtac "SSR	rand.157	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), b = (length l) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X); elpi z_report "rand.158" "1" ltac_term:(G)) | idtac "SSR	rand.158	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X); elpi z_report "rand.158" "2" ltac_term:(G)) | idtac "SSR	rand.158	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in b = X); elpi z_report "rand.158" "3" ltac_term:(G)) | idtac "SSR	rand.158	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in b = X); elpi z_report "rand.158" "4" ltac_term:(G)) | idtac "SSR	rand.158	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.158" "5" ltac_term:(G)) | idtac "SSR	rand.158	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in b = X); elpi z_report "rand.158" "6" ltac_term:(G)) | idtac "SSR	rand.158	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in _ = X); elpi z_report "rand.158" "7" ltac_term:(G)) | idtac "SSR	rand.158	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in b = X); elpi z_report "rand.158" "8" ltac_term:(G)) | idtac "SSR	rand.158	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in b = X); elpi z_report "rand.158" "9" ltac_term:(G)) | idtac "SSR	rand.158	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.158" "10" ltac_term:(G)) | idtac "SSR	rand.158	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in b = X); elpi z_report "rand.158" "11" ltac_term:(G)) | idtac "SSR	rand.158	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _ as X in b = X); elpi z_report "rand.158" "12" ltac_term:(G)) | idtac "SSR	rand.158	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd ((fst ((length (c :: l)), b)), ((length (l ++ l)) * (f 1 (f b a))))) = 
(f (g a) a) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = f X a); elpi z_report "rand.159" "1" ltac_term:(G)) | idtac "SSR	rand.159	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = X); elpi z_report "rand.159" "2" ltac_term:(G)) | idtac "SSR	rand.159	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.159" "3" ltac_term:(G)) | idtac "SSR	rand.159	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = f X _); elpi z_report "rand.159" "4" ltac_term:(G)) | idtac "SSR	rand.159	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = f X a); elpi z_report "rand.159" "5" ltac_term:(G)) | idtac "SSR	rand.159	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a as X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = f X _); elpi z_report "rand.159" "6" ltac_term:(G)) | idtac "SSR	rand.159	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X a); elpi z_report "rand.159" "7" ltac_term:(G)) | idtac "SSR	rand.159	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g a as X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = f X _); elpi z_report "rand.159" "8" ltac_term:(G)) | idtac "SSR	rand.159	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = f X _); elpi z_report "rand.159" "9" ltac_term:(G)) | idtac "SSR	rand.159	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g _); elpi z_report "rand.159" "10" ltac_term:(G)) | idtac "SSR	rand.159	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g _ in X in f X a); elpi z_report "rand.159" "11" ltac_term:(G)) | idtac "SSR	rand.159	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (fst (length (c :: l), b), length (l ++ l) * f 1 (f b a)) = f X _); elpi z_report "rand.159" "12" ltac_term:(G)) | idtac "SSR	rand.159	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((fst ((b + a), a)) + (snd ((3 + c), 2))) * (f 0 (f c (fst (a, 2))))) = 
(fst ((snd ((snd ((1 + 2), (b * 3))), (length l))), c)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in (snd X, c)); elpi z_report "rand.160" "1" ltac_term:(G)) | idtac "SSR	rand.160	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in (snd (1 + 2, b * 3), X)); elpi z_report "rand.160" "2" ltac_term:(G)) | idtac "SSR	rand.160	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in (fst (b + a, a) + snd (3 + c, 2)) * f 0 (f c (fst (a, 2))) = fst (snd (snd (1 + 2, b * 3), X), _)); elpi z_report "rand.160" "3" ltac_term:(G)) | idtac "SSR	rand.160	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in snd (snd (1 + 2, b * 3), X)); elpi z_report "rand.160" "4" ltac_term:(G)) | idtac "SSR	rand.160	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.160" "5" ltac_term:(G)) | idtac "SSR	rand.160	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in fst (snd (snd (1 + 2, b * 3), X), _)); elpi z_report "rand.160" "6" ltac_term:(G)) | idtac "SSR	rand.160	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.160" "7" ltac_term:(G)) | idtac "SSR	rand.160	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in (fst (b + a, a) + snd (3 + c, 2)) * f _ (f c (fst (a, 2))) = fst (snd (snd (1 + 2, b * 3), X), _)); elpi z_report "rand.160" "8" ltac_term:(G)) | idtac "SSR	rand.160	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.160" "9" ltac_term:(G)) | idtac "SSR	rand.160	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l as X in snd (snd (1 + 2, b * 3), X)); elpi z_report "rand.160" "10" ltac_term:(G)) | idtac "SSR	rand.160	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in snd (snd (1 + 2, b * 3), X)); elpi z_report "rand.160" "11" ltac_term:(G)) | idtac "SSR	rand.160	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in (snd (1 + 2, b * 3), X)); elpi z_report "rand.160" "12" ltac_term:(G)) | idtac "SSR	rand.160	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 = S X); elpi z_report "rand.161" "1" ltac_term:(G)) | idtac "SSR	rand.161	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.161" "2" ltac_term:(G)) | idtac "SSR	rand.161	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in _ = X); elpi z_report "rand.161" "3" ltac_term:(G)) | idtac "SSR	rand.161	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.161" "4" ltac_term:(G)) | idtac "SSR	rand.161	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.161" "5" ltac_term:(G)) | idtac "SSR	rand.161	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.161" "6" ltac_term:(G)) | idtac "SSR	rand.161	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X); elpi z_report "rand.161" "7" ltac_term:(G)) | idtac "SSR	rand.161	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in _ = S X); elpi z_report "rand.161" "8" ltac_term:(G)) | idtac "SSR	rand.161	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X); elpi z_report "rand.161" "9" ltac_term:(G)) | idtac "SSR	rand.161	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = S X); elpi z_report "rand.161" "10" ltac_term:(G)) | idtac "SSR	rand.161	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.161" "11" ltac_term:(G)) | idtac "SSR	rand.161	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in S X); elpi z_report "rand.161" "12" ltac_term:(G)) | idtac "SSR	rand.161	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((c * (fst ((f a a), (snd (2, a))))), (length l))) = 
(g (f (fst ((a + a), (fst (a, 0)))) (snd ((length l), (f b 1))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in (c * fst (f _ a, snd (S X, _)), length l)); elpi z_report "rand.162" "1" ltac_term:(G)) | idtac "SSR	rand.162	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (f _ a, snd (S X, _))); elpi z_report "rand.162" "2" ltac_term:(G)) | idtac "SSR	rand.162	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.162" "3" ltac_term:(G)) | idtac "SSR	rand.162	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in snd X); elpi z_report "rand.162" "4" ltac_term:(G)) | idtac "SSR	rand.162	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c * fst (f a a, snd (S X, a))); elpi z_report "rand.162" "5" ltac_term:(G)) | idtac "SSR	rand.162	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (f a a, snd (X, _))); elpi z_report "rand.162" "6" ltac_term:(G)) | idtac "SSR	rand.162	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in snd X); elpi z_report "rand.162" "7" ltac_term:(G)) | idtac "SSR	rand.162	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f b X); elpi z_report "rand.162" "8" ltac_term:(G)) | idtac "SSR	rand.162	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (S X, a)); elpi z_report "rand.162" "9" ltac_term:(G)) | idtac "SSR	rand.162	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.162" "10" ltac_term:(G)) | idtac "SSR	rand.162	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (length l, f _ X)); elpi z_report "rand.162" "11" ltac_term:(G)) | idtac "SSR	rand.162	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (f (fst (a + a, fst (a, 0))) (snd (_, f b X)))); elpi z_report "rand.162" "12" ltac_term:(G)) | idtac "SSR	rand.162	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f (snd ((c + (length l)), ((snd (1, a)) + (fst (0, 0))))) a) = 
(c + (snd ((0 + (fst (0, 2))), (fst (3, 2))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (0 + fst (0, 2), fst (3, S X))); elpi z_report "rand.163" "1" ltac_term:(G)) | idtac "SSR	rand.163	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (X, _)); elpi z_report "rand.163" "2" ltac_term:(G)) | idtac "SSR	rand.163	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in fst (0, X)); elpi z_report "rand.163" "3" ltac_term:(G)) | idtac "SSR	rand.163	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst (0, X)); elpi z_report "rand.163" "4" ltac_term:(G)) | idtac "SSR	rand.163	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (3, S X)); elpi z_report "rand.163" "5" ltac_term:(G)) | idtac "SSR	rand.163	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (snd (c + length l, snd (1, a) + fst (0, 0))) a = c + snd (0 + fst (0, 2), fst (3, S X))); elpi z_report "rand.163" "6" ltac_term:(G)) | idtac "SSR	rand.163	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (_ + fst (_, S X), fst (3, 2))); elpi z_report "rand.163" "7" ltac_term:(G)) | idtac "SSR	rand.163	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.163" "8" ltac_term:(G)) | idtac "SSR	rand.163	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (3, X)); elpi z_report "rand.163" "9" ltac_term:(G)) | idtac "SSR	rand.163	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.163" "10" ltac_term:(G)) | idtac "SSR	rand.163	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst (3, X)); elpi z_report "rand.163" "11" ltac_term:(G)) | idtac "SSR	rand.163	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (3, S X)); elpi z_report "rand.163" "12" ltac_term:(G)) | idtac "SSR	rand.163	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = (fst (0, b)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, b); elpi z_report "rand.164" "1" ltac_term:(G)) | idtac "SSR	rand.164	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}((0, b) in X in _ = X); elpi z_report "rand.164" "2" ltac_term:(G)) | idtac "SSR	rand.164	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = fst X); elpi z_report "rand.164" "3" ltac_term:(G)) | idtac "SSR	rand.164	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, b) in X in 0 = X); elpi z_report "rand.164" "4" ltac_term:(G)) | idtac "SSR	rand.164	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0, b); elpi z_report "rand.164" "5" ltac_term:(G)) | idtac "SSR	rand.164	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((0, _) in X in fst X); elpi z_report "rand.164" "6" ltac_term:(G)) | idtac "SSR	rand.164	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, b); elpi z_report "rand.164" "7" ltac_term:(G)) | idtac "SSR	rand.164	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}((_, b) in X in fst X); elpi z_report "rand.164" "8" ltac_term:(G)) | idtac "SSR	rand.164	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((0, b) as X in fst X); elpi z_report "rand.164" "9" ltac_term:(G)) | idtac "SSR	rand.164	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, _); elpi z_report "rand.164" "10" ltac_term:(G)) | idtac "SSR	rand.164	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, b); elpi z_report "rand.164" "11" ltac_term:(G)) | idtac "SSR	rand.164	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = fst X); elpi z_report "rand.164" "12" ltac_term:(G)) | idtac "SSR	rand.164	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length ((length l) :: (b :: (l ++ l)))) = 0 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (length l :: _ :: X)); elpi z_report "rand.165" "1" ltac_term:(G)) | idtac "SSR	rand.165	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (length l :: _ :: X) = 0); elpi z_report "rand.165" "2" ltac_term:(G)) | idtac "SSR	rand.165	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(l ++ l); elpi z_report "rand.165" "3" ltac_term:(G)) | idtac "SSR	rand.165	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in length (length l :: X)); elpi z_report "rand.165" "4" ltac_term:(G)) | idtac "SSR	rand.165	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(l ++ l as X in length (length _ :: b :: X) = _); elpi z_report "rand.165" "5" ltac_term:(G)) | idtac "SSR	rand.165	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ in X in _ :: X); elpi z_report "rand.165" "6" ltac_term:(G)) | idtac "SSR	rand.165	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ _ in X in length l :: X); elpi z_report "rand.165" "7" ltac_term:(G)) | idtac "SSR	rand.165	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (length l :: b :: X) = 0); elpi z_report "rand.165" "8" ltac_term:(G)) | idtac "SSR	rand.165	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length (length l :: _ :: X)); elpi z_report "rand.165" "9" ltac_term:(G)) | idtac "SSR	rand.165	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length l :: _ :: X); elpi z_report "rand.165" "10" ltac_term:(G)) | idtac "SSR	rand.165	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ :: _ :: X); elpi z_report "rand.165" "11" ltac_term:(G)) | idtac "SSR	rand.165	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l); elpi z_report "rand.165" "12" ltac_term:(G)) | idtac "SSR	rand.165	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((f 3 (fst ((c * 1), 2))) * (fst ((g b), (snd (0, (f 3 0)))))) = 0 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (c * 1, S X)); elpi z_report "rand.166" "1" ltac_term:(G)) | idtac "SSR	rand.166	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.166" "2" ltac_term:(G)) | idtac "SSR	rand.166	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.166" "3" ltac_term:(G)) | idtac "SSR	rand.166	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in f 3 X); elpi z_report "rand.166" "4" ltac_term:(G)) | idtac "SSR	rand.166	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.166" "5" ltac_term:(G)) | idtac "SSR	rand.166	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.166" "6" ltac_term:(G)) | idtac "SSR	rand.166	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in f 3 X); elpi z_report "rand.166" "7" ltac_term:(G)) | idtac "SSR	rand.166	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f (S X) (fst (c * 1, 2)) * fst (g b, snd (0, f 3 0)) = 0); elpi z_report "rand.166" "8" ltac_term:(G)) | idtac "SSR	rand.166	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.166" "9" ltac_term:(G)) | idtac "SSR	rand.166	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (_, snd (_, f X _))); elpi z_report "rand.166" "10" ltac_term:(G)) | idtac "SSR	rand.166	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (_, f X 0)); elpi z_report "rand.166" "11" ltac_term:(G)) | idtac "SSR	rand.166	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.166" "12" ltac_term:(G)) | idtac "SSR	rand.166	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(length (((f 0 3) + (0 + b)) :: ((g 3) :: l))) = 
(g (1 * (1 + (snd (3, a))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.167" "1" ltac_term:(G)) | idtac "SSR	rand.167	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in S X); elpi z_report "rand.167" "2" ltac_term:(G)) | idtac "SSR	rand.167	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.167" "3" ltac_term:(G)) | idtac "SSR	rand.167	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (S (S X), _)); elpi z_report "rand.167" "4" ltac_term:(G)) | idtac "SSR	rand.167	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.167" "5" ltac_term:(G)) | idtac "SSR	rand.167	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f 0 (S (S X)) + (0 + b)); elpi z_report "rand.167" "6" ltac_term:(G)) | idtac "SSR	rand.167	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f _ X + (0 + b)); elpi z_report "rand.167" "7" ltac_term:(G)) | idtac "SSR	rand.167	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.167" "8" ltac_term:(G)) | idtac "SSR	rand.167	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in length (f 0 3 + (0 + b) :: g 3 :: l) = X); elpi z_report "rand.167" "9" ltac_term:(G)) | idtac "SSR	rand.167	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in 1 * (X + snd (3, a))); elpi z_report "rand.167" "10" ltac_term:(G)) | idtac "SSR	rand.167	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "rand.167" "11" ltac_term:(G)) | idtac "SSR	rand.167	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (X * (S _ + snd (3, a)))); elpi z_report "rand.167" "12" ltac_term:(G)) | idtac "SSR	rand.167	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (c * 2) = 
((fst ((snd (a, (c * 1))), 0)) + 2) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.168" "1" ltac_term:(G)) | idtac "SSR	rand.168	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (snd (a, c * 1), 0) + S X); elpi z_report "rand.168" "2" ltac_term:(G)) | idtac "SSR	rand.168	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.168" "3" ltac_term:(G)) | idtac "SSR	rand.168	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.168" "4" ltac_term:(G)) | idtac "SSR	rand.168	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in c * 2 = fst (snd (a, c * 1), 0) + X); elpi z_report "rand.168" "5" ltac_term:(G)) | idtac "SSR	rand.168	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X + 2); elpi z_report "rand.168" "6" ltac_term:(G)) | idtac "SSR	rand.168	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (snd (a, c * X), 0)); elpi z_report "rand.168" "7" ltac_term:(G)) | idtac "SSR	rand.168	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (snd (a, c * 1), 0) + S X); elpi z_report "rand.168" "8" ltac_term:(G)) | idtac "SSR	rand.168	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in _ * S (S _) = fst (snd (a, c * 1), 0) + S X); elpi z_report "rand.168" "9" ltac_term:(G)) | idtac "SSR	rand.168	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in fst (snd (a, c * 1), 0) + X); elpi z_report "rand.168" "10" ltac_term:(G)) | idtac "SSR	rand.168	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in _ * 2 = fst (snd (a, c * 1), 0) + S X); elpi z_report "rand.168" "11" ltac_term:(G)) | idtac "SSR	rand.168	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ * S X); elpi z_report "rand.168" "12" ltac_term:(G)) | idtac "SSR	rand.168	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(((f (a * 2) (b + 0)) * (length (3 :: l))) + c) = (length l) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in f (a * 2) (b + 0) * length (3 :: l) + c = X); elpi z_report "rand.169" "1" ltac_term:(G)) | idtac "SSR	rand.169	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.169" "2" ltac_term:(G)) | idtac "SSR	rand.169	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.169" "3" ltac_term:(G)) | idtac "SSR	rand.169	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in f (a * 2) (b + 0) * length (3 :: l) + _ = X); elpi z_report "rand.169" "4" ltac_term:(G)) | idtac "SSR	rand.169	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.169" "5" ltac_term:(G)) | idtac "SSR	rand.169	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _ as X in f (a * 2) (b + 0) * length (3 :: l) + c = X); elpi z_report "rand.169" "6" ltac_term:(G)) | idtac "SSR	rand.169	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _); elpi z_report "rand.169" "7" ltac_term:(G)) | idtac "SSR	rand.169	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in f (a * 2) (b + 0) * length (3 :: l) + _ = X); elpi z_report "rand.169" "8" ltac_term:(G)) | idtac "SSR	rand.169	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(length _); elpi z_report "rand.169" "9" ltac_term:(G)) | idtac "SSR	rand.169	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in f (a * 2) (b + 0) * length (3 :: l) + c = X); elpi z_report "rand.169" "10" ltac_term:(G)) | idtac "SSR	rand.169	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l); elpi z_report "rand.169" "11" ltac_term:(G)) | idtac "SSR	rand.169	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ in X in f (a * 2) (b + 0) * length (3 :: l) + c = X); elpi z_report "rand.169" "12" ltac_term:(G)) | idtac "SSR	rand.169	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((fst ((f b 0), 2)) * (g (length l))) (length ((length l) :: (1 :: l)))) 
= (g ((length (l ++ l)) + (snd ((f 0 3), c)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.170" "1" ltac_term:(G)) | idtac "SSR	rand.170	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.170" "2" ltac_term:(G)) | idtac "SSR	rand.170	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (f 0 X, c)); elpi z_report "rand.170" "3" ltac_term:(G)) | idtac "SSR	rand.170	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X :: _); elpi z_report "rand.170" "4" ltac_term:(G)) | idtac "SSR	rand.170	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X :: l); elpi z_report "rand.170" "5" ltac_term:(G)) | idtac "SSR	rand.170	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length l :: X); elpi z_report "rand.170" "6" ltac_term:(G)) | idtac "SSR	rand.170	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.170" "7" ltac_term:(G)) | idtac "SSR	rand.170	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in g (length (l ++ l) + snd (f 0 (S (S X)), _))); elpi z_report "rand.170" "8" ltac_term:(G)) | idtac "SSR	rand.170	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in length (l ++ l) + snd (f _ (S (S X)), c)); elpi z_report "rand.170" "9" ltac_term:(G)) | idtac "SSR	rand.170	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (f b 0, S X)); elpi z_report "rand.170" "10" ltac_term:(G)) | idtac "SSR	rand.170	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f b 0, S X) * g (length l)); elpi z_report "rand.170" "11" ltac_term:(G)) | idtac "SSR	rand.170	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (fst (f b 0, S X) * g (length l)) (length (length l :: 1 :: l)) = g (length (l ++ _) + snd (f 0 3, c))); elpi z_report "rand.170" "12" ltac_term:(G)) | idtac "SSR	rand.170	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (3, (g (g (3 * b))))) = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.171" "1" ltac_term:(G)) | idtac "SSR	rand.171	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.171" "2" ltac_term:(G)) | idtac "SSR	rand.171	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S (S X)); elpi z_report "rand.171" "3" ltac_term:(G)) | idtac "SSR	rand.171	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.171" "4" ltac_term:(G)) | idtac "SSR	rand.171	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.171" "5" ltac_term:(G)) | idtac "SSR	rand.171	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (S (S X), g (g (3 * b))) = b); elpi z_report "rand.171" "6" ltac_term:(G)) | idtac "SSR	rand.171	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (3, g (g (S (S X) * b)))); elpi z_report "rand.171" "7" ltac_term:(G)) | idtac "SSR	rand.171	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.171" "8" ltac_term:(G)) | idtac "SSR	rand.171	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in (S (S (S _)), g (g (S (S X) * b)))); elpi z_report "rand.171" "9" ltac_term:(G)) | idtac "SSR	rand.171	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (S (S X), g (g (3 * b)))); elpi z_report "rand.171" "10" ltac_term:(G)) | idtac "SSR	rand.171	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (g (S (S X) * _))); elpi z_report "rand.171" "11" ltac_term:(G)) | idtac "SSR	rand.171	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in snd (S (S X), g (g (3 * b))) = _); elpi z_report "rand.171" "12" ltac_term:(G)) | idtac "SSR	rand.171	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (f b ((f 3 (fst (a, b))) * (g 0))) 
= b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in f b (f 3 (fst (a, b)) * X)); elpi z_report "rand.172" "1" ltac_term:(G)) | idtac "SSR	rand.172	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in f b (f 3 (fst (a, b)) * X)); elpi z_report "rand.172" "2" ltac_term:(G)) | idtac "SSR	rand.172	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in f b (f 3 (fst (a, b)) * X)); elpi z_report "rand.172" "3" ltac_term:(G)) | idtac "SSR	rand.172	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0); elpi z_report "rand.172" "4" ltac_term:(G)) | idtac "SSR	rand.172	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0 as X in f 3 (fst (a, b)) * X); elpi z_report "rand.172" "5" ltac_term:(G)) | idtac "SSR	rand.172	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g _ in X in f _ X); elpi z_report "rand.172" "6" ltac_term:(G)) | idtac "SSR	rand.172	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g _ in X in f b X); elpi z_report "rand.172" "7" ltac_term:(G)) | idtac "SSR	rand.172	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in f b (f 3 (fst (a, b)) * X) = _); elpi z_report "rand.172" "8" ltac_term:(G)) | idtac "SSR	rand.172	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0); elpi z_report "rand.172" "9" ltac_term:(G)) | idtac "SSR	rand.172	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g 0); elpi z_report "rand.172" "10" ltac_term:(G)) | idtac "SSR	rand.172	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in f _ (f 3 (fst (a, b)) * X)); elpi z_report "rand.172" "11" ltac_term:(G)) | idtac "SSR	rand.172	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.172" "12" ltac_term:(G)) | idtac "SSR	rand.172	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = 
((fst (((1 + 2) + (f 2 c)), (snd ((length l), (snd (0, 1)))))) * (length l)) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "rand.173" "1" ltac_term:(G)) | idtac "SSR	rand.173	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l as X in snd (X, snd (0, 1))); elpi z_report "rand.173" "2" ltac_term:(G)) | idtac "SSR	rand.173	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.173" "3" ltac_term:(G)) | idtac "SSR	rand.173	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in (1 + 2 + f 2 c, snd (X, snd (0, 1)))); elpi z_report "rand.173" "4" ltac_term:(G)) | idtac "SSR	rand.173	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length _); elpi z_report "rand.173" "5" ltac_term:(G)) | idtac "SSR	rand.173	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in fst (1 + 2 + f 2 c, snd (length l, snd (0, 1))) * X); elpi z_report "rand.173" "6" ltac_term:(G)) | idtac "SSR	rand.173	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (1 + 2 + f 2 c, snd (length l, snd (0, 1))) * X); elpi z_report "rand.173" "7" ltac_term:(G)) | idtac "SSR	rand.173	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "rand.173" "8" ltac_term:(G)) | idtac "SSR	rand.173	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (1 + 2 + f 2 c, snd (length l, snd (0, 1))) * X); elpi z_report "rand.173" "9" ltac_term:(G)) | idtac "SSR	rand.173	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length _ as X in fst (1 + 2 + f 2 c, snd (X, snd (0, 1)))); elpi z_report "rand.173" "10" ltac_term:(G)) | idtac "SSR	rand.173	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in c = X); elpi z_report "rand.173" "11" ltac_term:(G)) | idtac "SSR	rand.173	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (1 + 2 + f 2 c, snd (X, snd (0, S _)))); elpi z_report "rand.173" "12" ltac_term:(G)) | idtac "SSR	rand.173	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.174" "1" ltac_term:(G)) | idtac "SSR	rand.174	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = 3); elpi z_report "rand.174" "2" ltac_term:(G)) | idtac "SSR	rand.174	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.174" "3" ltac_term:(G)) | idtac "SSR	rand.174	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X = 3); elpi z_report "rand.174" "4" ltac_term:(G)) | idtac "SSR	rand.174	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.174" "5" ltac_term:(G)) | idtac "SSR	rand.174	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 1 = S X); elpi z_report "rand.174" "6" ltac_term:(G)) | idtac "SSR	rand.174	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.174" "7" ltac_term:(G)) | idtac "SSR	rand.174	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.174" "8" ltac_term:(G)) | idtac "SSR	rand.174	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.174" "9" ltac_term:(G)) | idtac "SSR	rand.174	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S (S X)); elpi z_report "rand.174" "10" ltac_term:(G)) | idtac "SSR	rand.174	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = 3); elpi z_report "rand.174" "11" ltac_term:(G)) | idtac "SSR	rand.174	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.174" "12" ltac_term:(G)) | idtac "SSR	rand.174	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((g 2) * ((snd (2, 3)) * 0)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.175" "1" ltac_term:(G)) | idtac "SSR	rand.175	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in snd (X, 3)); elpi z_report "rand.175" "2" ltac_term:(G)) | idtac "SSR	rand.175	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S X)); elpi z_report "rand.175" "3" ltac_term:(G)) | idtac "SSR	rand.175	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.175" "4" ltac_term:(G)) | idtac "SSR	rand.175	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g 2 * (snd (S X, 3) * _)); elpi z_report "rand.175" "5" ltac_term:(G)) | idtac "SSR	rand.175	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (X, 3)); elpi z_report "rand.175" "6" ltac_term:(G)) | idtac "SSR	rand.175	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (S X, 3) * _); elpi z_report "rand.175" "7" ltac_term:(G)) | idtac "SSR	rand.175	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.175" "8" ltac_term:(G)) | idtac "SSR	rand.175	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.175" "9" ltac_term:(G)) | idtac "SSR	rand.175	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.175" "10" ltac_term:(G)) | idtac "SSR	rand.175	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in length _ = g 2 * (snd (2, S (S X)) * _)); elpi z_report "rand.175" "11" ltac_term:(G)) | idtac "SSR	rand.175	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.175" "12" ltac_term:(G)) | idtac "SSR	rand.175	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(0 * (snd ((fst ((c * c), 0)), (g b)))) = c .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in snd (fst (c * c, 0), X)); elpi z_report "rand.176" "1" ltac_term:(G)) | idtac "SSR	rand.176	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b as X in 0 * snd (fst (c * c, 0), X) = c); elpi z_report "rand.176" "2" ltac_term:(G)) | idtac "SSR	rand.176	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g b as X in snd (fst (c * c, 0), X)); elpi z_report "rand.176" "3" ltac_term:(G)) | idtac "SSR	rand.176	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in _ * X = _); elpi z_report "rand.176" "4" ltac_term:(G)) | idtac "SSR	rand.176	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 * snd (fst (c * c, 0), X) = c); elpi z_report "rand.176" "5" ltac_term:(G)) | idtac "SSR	rand.176	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b in X in (fst (c * c, _), X)); elpi z_report "rand.176" "6" ltac_term:(G)) | idtac "SSR	rand.176	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b in X in (fst (c * c, 0), X)); elpi z_report "rand.176" "7" ltac_term:(G)) | idtac "SSR	rand.176	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g _ as X in snd (fst (c * c, 0), X)); elpi z_report "rand.176" "8" ltac_term:(G)) | idtac "SSR	rand.176	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g b as X in snd (fst (c * c, 0), X)); elpi z_report "rand.176" "9" ltac_term:(G)) | idtac "SSR	rand.176	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g _ as X in snd (fst (c * c, 0), X)); elpi z_report "rand.176" "10" ltac_term:(G)) | idtac "SSR	rand.176	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in snd (fst (c * c, 0), X)); elpi z_report "rand.176" "11" ltac_term:(G)) | idtac "SSR	rand.176	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 * snd (fst (c * c, 0), X) = _); elpi z_report "rand.176" "12" ltac_term:(G)) | idtac "SSR	rand.176	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((length ((l ++ l) ++ (2 :: l))) + ((length (l ++ l)) * (f (1 * 2) (g c)))) 
= (f (f ((g 3) * c) b) (length (l ++ l))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(l ++ _ as X in length ((l ++ l) ++ 2 :: l) + length (l ++ l) * f (1 * 2) (g c) = f (f (g 3 * _) _) (length X)); elpi z_report "rand.177" "1" ltac_term:(G)) | idtac "SSR	rand.177	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.177" "2" ltac_term:(G)) | idtac "SSR	rand.177	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X * f (1 * 2) (g c)); elpi z_report "rand.177" "3" ltac_term:(G)) | idtac "SSR	rand.177	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l ++ l as X in length (X ++ 2 :: l)); elpi z_report "rand.177" "4" ltac_term:(G)) | idtac "SSR	rand.177	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in length ((l ++ l) ++ 2 :: l) + length (l ++ l) * f (1 * 2) (g c) = X); elpi z_report "rand.177" "5" ltac_term:(G)) | idtac "SSR	rand.177	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.177" "6" ltac_term:(G)) | idtac "SSR	rand.177	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.177" "7" ltac_term:(G)) | idtac "SSR	rand.177	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.177" "8" ltac_term:(G)) | idtac "SSR	rand.177	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.177" "9" ltac_term:(G)) | idtac "SSR	rand.177	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.177" "10" ltac_term:(G)) | idtac "SSR	rand.177	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length ((l ++ l) ++ 2 :: l) + length X * f (1 * 2) (g c)); elpi z_report "rand.177" "11" ltac_term:(G)) | idtac "SSR	rand.177	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in length X); elpi z_report "rand.177" "12" ltac_term:(G)) | idtac "SSR	rand.177	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (0, c)) = 
(length ((length (l ++ l)) :: l)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X); elpi z_report "rand.178" "1" ltac_term:(G)) | idtac "SSR	rand.178	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (0, _) = length (length X :: l)); elpi z_report "rand.178" "2" ltac_term:(G)) | idtac "SSR	rand.178	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _); elpi z_report "rand.178" "3" ltac_term:(G)) | idtac "SSR	rand.178	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.178" "4" ltac_term:(G)) | idtac "SSR	rand.178	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ ++ _); elpi z_report "rand.178" "5" ltac_term:(G)) | idtac "SSR	rand.178	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length X); elpi z_report "rand.178" "6" ltac_term:(G)) | idtac "SSR	rand.178	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in length X :: l); elpi z_report "rand.178" "7" ltac_term:(G)) | idtac "SSR	rand.178	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.178" "8" ltac_term:(G)) | idtac "SSR	rand.178	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l as X in snd (0, c) = length (length X :: l)); elpi z_report "rand.178" "9" ltac_term:(G)) | idtac "SSR	rand.178	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length (length X :: l)); elpi z_report "rand.178" "10" ltac_term:(G)) | idtac "SSR	rand.178	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.178" "11" ltac_term:(G)) | idtac "SSR	rand.178	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l); elpi z_report "rand.178" "12" ltac_term:(G)) | idtac "SSR	rand.178	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (1, (f ((g 1) + (f 1 a)) (g (g c))))) = 
(g ((fst ((length l), (length l))) + (3 * (f a 2)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.179" "1" ltac_term:(G)) | idtac "SSR	rand.179	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g 1 + f X _); elpi z_report "rand.179" "2" ltac_term:(G)) | idtac "SSR	rand.179	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (X, f (g 1 + f 1 a) (g (g c)))); elpi z_report "rand.179" "3" ltac_term:(G)) | idtac "SSR	rand.179	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.179" "4" ltac_term:(G)) | idtac "SSR	rand.179	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X) * f a 2); elpi z_report "rand.179" "5" ltac_term:(G)) | idtac "SSR	rand.179	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in f (X + f 1 a) (g (g c))); elpi z_report "rand.179" "6" ltac_term:(G)) | idtac "SSR	rand.179	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.179" "7" ltac_term:(G)) | idtac "SSR	rand.179	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (1, f (g 1 + f X _) (g (g c))) = g (fst (length l, length l) + 3 * f a 2)); elpi z_report "rand.179" "8" ltac_term:(G)) | idtac "SSR	rand.179	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.179" "9" ltac_term:(G)) | idtac "SSR	rand.179	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in f a (S X)); elpi z_report "rand.179" "10" ltac_term:(G)) | idtac "SSR	rand.179	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in snd (X, f (g 1 + f 1 a) (g (g c))) = g (fst (length l, _) + 3 * f a 2)); elpi z_report "rand.179" "11" ltac_term:(G)) | idtac "SSR	rand.179	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.179" "12" ltac_term:(G)) | idtac "SSR	rand.179	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(fst (3, (fst ((c * (fst (c, 2))), (g (fst (c, 2))))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in (_, S X)); elpi z_report "rand.180" "1" ltac_term:(G)) | idtac "SSR	rand.180	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (X, fst (c * fst (c, 2), g (fst (c, 2))))); elpi z_report "rand.180" "2" ltac_term:(G)) | idtac "SSR	rand.180	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in fst (S (S X), fst (c * fst (c, 2), g (fst (c, 2))))); elpi z_report "rand.180" "3" ltac_term:(G)) | idtac "SSR	rand.180	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (_, S X)); elpi z_report "rand.180" "4" ltac_term:(G)) | idtac "SSR	rand.180	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X); elpi z_report "rand.180" "5" ltac_term:(G)) | idtac "SSR	rand.180	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.180" "6" ltac_term:(G)) | idtac "SSR	rand.180	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in fst (S (S X), fst (c * fst (c, 2), g (fst (c, 2))))); elpi z_report "rand.180" "7" ltac_term:(G)) | idtac "SSR	rand.180	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst X); elpi z_report "rand.180" "8" ltac_term:(G)) | idtac "SSR	rand.180	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.180" "9" ltac_term:(G)) | idtac "SSR	rand.180	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (c, S X)); elpi z_report "rand.180" "10" ltac_term:(G)) | idtac "SSR	rand.180	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (S (S X), fst (c * fst (c, 2), g (fst (c, 2))))); elpi z_report "rand.180" "11" ltac_term:(G)) | idtac "SSR	rand.180	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.180" "12" ltac_term:(G)) | idtac "SSR	rand.180	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(f ((g (fst (b, c))) * (f (2 * a) (c + 2))) (((f 3 1) * a) * 3)) = (0 + 3) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X * 3); elpi z_report "rand.181" "1" ltac_term:(G)) | idtac "SSR	rand.181	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.181" "2" ltac_term:(G)) | idtac "SSR	rand.181	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X * a); elpi z_report "rand.181" "3" ltac_term:(G)) | idtac "SSR	rand.181	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.181" "4" ltac_term:(G)) | idtac "SSR	rand.181	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.181" "5" ltac_term:(G)) | idtac "SSR	rand.181	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f 3 X * a); elpi z_report "rand.181" "6" ltac_term:(G)) | idtac "SSR	rand.181	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.181" "7" ltac_term:(G)) | idtac "SSR	rand.181	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (g (fst (b, c)) * f (2 * a) (c + 2)) (f 3 1 * a * S (S X))); elpi z_report "rand.181" "8" ltac_term:(G)) | idtac "SSR	rand.181	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X)); elpi z_report "rand.181" "9" ltac_term:(G)) | idtac "SSR	rand.181	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.181" "10" ltac_term:(G)) | idtac "SSR	rand.181	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f (g (fst (b, c)) * f (2 * a) (c + 2)) (f 3 1 * a * S (S X))); elpi z_report "rand.181" "11" ltac_term:(G)) | idtac "SSR	rand.181	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.181" "12" ltac_term:(G)) | idtac "SSR	rand.181	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (snd (1, (fst (2, (fst (2, a))))))) = (g (g ((1 * b) + (snd (c, 2))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.182" "1" ltac_term:(G)) | idtac "SSR	rand.182	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (snd (X, fst (2, fst (2, a)))) = g (g (1 * b + snd (c, 2)))); elpi z_report "rand.182" "2" ltac_term:(G)) | idtac "SSR	rand.182	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (1, fst (S X, fst (2, _)))); elpi z_report "rand.182" "3" ltac_term:(G)) | idtac "SSR	rand.182	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in snd (1, fst X)); elpi z_report "rand.182" "4" ltac_term:(G)) | idtac "SSR	rand.182	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (S X, fst (2, a))); elpi z_report "rand.182" "5" ltac_term:(G)) | idtac "SSR	rand.182	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g (snd (_, X)) = g (g (1 * _ + snd (c, 2)))); elpi z_report "rand.182" "6" ltac_term:(G)) | idtac "SSR	rand.182	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X * _); elpi z_report "rand.182" "7" ltac_term:(G)) | idtac "SSR	rand.182	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (c, S X)); elpi z_report "rand.182" "8" ltac_term:(G)) | idtac "SSR	rand.182	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (snd (X, fst (_, fst (2, a)))) = g (g (1 * b + snd (c, 2)))); elpi z_report "rand.182" "9" ltac_term:(G)) | idtac "SSR	rand.182	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (2, fst X)); elpi z_report "rand.182" "10" ltac_term:(G)) | idtac "SSR	rand.182	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.182" "11" ltac_term:(G)) | idtac "SSR	rand.182	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (g (1 * _ + snd (c, S X)))); elpi z_report "rand.182" "12" ltac_term:(G)) | idtac "SSR	rand.182	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(b + (g (fst ((1 * a), (length l))))) = (c + 2) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in b + g (fst (1 * a, length l)) = c + S X); elpi z_report "rand.183" "1" ltac_term:(G)) | idtac "SSR	rand.183	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in X * a); elpi z_report "rand.183" "2" ltac_term:(G)) | idtac "SSR	rand.183	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.183" "3" ltac_term:(G)) | idtac "SSR	rand.183	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in g (fst (X * a, length l))); elpi z_report "rand.183" "4" ltac_term:(G)) | idtac "SSR	rand.183	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c + S X); elpi z_report "rand.183" "5" ltac_term:(G)) | idtac "SSR	rand.183	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (X * a, length l)); elpi z_report "rand.183" "6" ltac_term:(G)) | idtac "SSR	rand.183	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ + g (fst (1 * a, length l)) = _ + S X); elpi z_report "rand.183" "7" ltac_term:(G)) | idtac "SSR	rand.183	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in b + g (fst (1 * a, length l)) = X); elpi z_report "rand.183" "8" ltac_term:(G)) | idtac "SSR	rand.183	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.183" "9" ltac_term:(G)) | idtac "SSR	rand.183	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.183" "10" ltac_term:(G)) | idtac "SSR	rand.183	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.183" "11" ltac_term:(G)) | idtac "SSR	rand.183	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ + S X); elpi z_report "rand.183" "12" ltac_term:(G)) | idtac "SSR	rand.183	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
((length (l ++ (3 :: l))) + ((snd ((0 * a), (g b))) * a)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_ * a, X) * a); elpi z_report "rand.184" "1" ltac_term:(G)) | idtac "SSR	rand.184	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(g _ in X in (0 * a, X)); elpi z_report "rand.184" "2" ltac_term:(G)) | idtac "SSR	rand.184	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in length (l ++ 3 :: l) + snd (_, X) * a); elpi z_report "rand.184" "3" ltac_term:(G)) | idtac "SSR	rand.184	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g _); elpi z_report "rand.184" "4" ltac_term:(G)) | idtac "SSR	rand.184	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (0 * a, X) * a); elpi z_report "rand.184" "5" ltac_term:(G)) | idtac "SSR	rand.184	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (0 * a, X)); elpi z_report "rand.184" "6" ltac_term:(G)) | idtac "SSR	rand.184	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b as X in length (_ ++ 3 :: l) + snd (0 * a, X) * _); elpi z_report "rand.184" "7" ltac_term:(G)) | idtac "SSR	rand.184	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in (0 * a, X)); elpi z_report "rand.184" "8" ltac_term:(G)) | idtac "SSR	rand.184	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g b); elpi z_report "rand.184" "9" ltac_term:(G)) | idtac "SSR	rand.184	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ in X in snd X); elpi z_report "rand.184" "10" ltac_term:(G)) | idtac "SSR	rand.184	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _); elpi z_report "rand.184" "11" ltac_term:(G)) | idtac "SSR	rand.184	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g _ as X in snd (0 * _, X) * _); elpi z_report "rand.184" "12" ltac_term:(G)) | idtac "SSR	rand.184	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (c * (f 3 2)) = c .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (S (S X)) 2); elpi z_report "rand.185" "1" ltac_term:(G)) | idtac "SSR	rand.185	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.185" "2" ltac_term:(G)) | idtac "SSR	rand.185	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in c * f (S (S X)) 2); elpi z_report "rand.185" "3" ltac_term:(G)) | idtac "SSR	rand.185	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * f (S (S X)) 2); elpi z_report "rand.185" "4" ltac_term:(G)) | idtac "SSR	rand.185	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.185" "5" ltac_term:(G)) | idtac "SSR	rand.185	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.185" "6" ltac_term:(G)) | idtac "SSR	rand.185	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.185" "7" ltac_term:(G)) | idtac "SSR	rand.185	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in _ * f 3 (S X)); elpi z_report "rand.185" "8" ltac_term:(G)) | idtac "SSR	rand.185	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f 3 (S X)); elpi z_report "rand.185" "9" ltac_term:(G)) | idtac "SSR	rand.185	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.185" "10" ltac_term:(G)) | idtac "SSR	rand.185	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.185" "11" ltac_term:(G)) | idtac "SSR	rand.185	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.185" "12" ltac_term:(G)) | idtac "SSR	rand.185	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), ((g (2 + 2)) + b) = (snd (0, 3)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.186" "1" ltac_term:(G)) | idtac "SSR	rand.186	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.186" "2" ltac_term:(G)) | idtac "SSR	rand.186	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (2 + S X) + b); elpi z_report "rand.186" "3" ltac_term:(G)) | idtac "SSR	rand.186	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S X + 2) + _); elpi z_report "rand.186" "4" ltac_term:(G)) | idtac "SSR	rand.186	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.186" "5" ltac_term:(G)) | idtac "SSR	rand.186	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.186" "6" ltac_term:(G)) | idtac "SSR	rand.186	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.186" "7" ltac_term:(G)) | idtac "SSR	rand.186	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.186" "8" ltac_term:(G)) | idtac "SSR	rand.186	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g (2 + 2) + _ = snd (_, X)); elpi z_report "rand.186" "9" ltac_term:(G)) | idtac "SSR	rand.186	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in g (2 + 2) + _ = snd (0, X)); elpi z_report "rand.186" "10" ltac_term:(G)) | idtac "SSR	rand.186	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.186" "11" ltac_term:(G)) | idtac "SSR	rand.186	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (2 + S X)); elpi z_report "rand.186" "12" ltac_term:(G)) | idtac "SSR	rand.186	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
(fst (2, ((fst ((c + c), 1)) * (f 1 (snd (2, 1)))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (S _) (snd (2, X))); elpi z_report "rand.187" "1" ltac_term:(G)) | idtac "SSR	rand.187	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in fst (c + c, 1) * f 1 X); elpi z_report "rand.187" "2" ltac_term:(G)) | idtac "SSR	rand.187	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "rand.187" "3" ltac_term:(G)) | idtac "SSR	rand.187	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (X, fst (c + c, 1) * f _ (snd (2, 1)))); elpi z_report "rand.187" "4" ltac_term:(G)) | idtac "SSR	rand.187	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.187" "5" ltac_term:(G)) | idtac "SSR	rand.187	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.187" "6" ltac_term:(G)) | idtac "SSR	rand.187	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in (_, X)); elpi z_report "rand.187" "7" ltac_term:(G)) | idtac "SSR	rand.187	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in 1 = fst (2, fst (c + c, _) * f 1 (snd (S X, 1)))); elpi z_report "rand.187" "8" ltac_term:(G)) | idtac "SSR	rand.187	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in 1 = fst (2, fst (c + c, X) * f 1 (snd (2, 1)))); elpi z_report "rand.187" "9" ltac_term:(G)) | idtac "SSR	rand.187	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in fst (c + c, 1) * f (S _) (snd (2, X))); elpi z_report "rand.187" "10" ltac_term:(G)) | idtac "SSR	rand.187	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X); elpi z_report "rand.187" "11" ltac_term:(G)) | idtac "SSR	rand.187	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.187" "12" ltac_term:(G)) | idtac "SSR	rand.187	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 0 = 
(f ((length l) + (f 0 (snd (2, 0)))) 2) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (S X, _)); elpi z_report "rand.188" "1" ltac_term:(G)) | idtac "SSR	rand.188	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.188" "2" ltac_term:(G)) | idtac "SSR	rand.188	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.188" "3" ltac_term:(G)) | idtac "SSR	rand.188	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ = f (length l + f 0 (snd (2, 0))) (S X)); elpi z_report "rand.188" "4" ltac_term:(G)) | idtac "SSR	rand.188	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in 0 = X); elpi z_report "rand.188" "5" ltac_term:(G)) | idtac "SSR	rand.188	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.188" "6" ltac_term:(G)) | idtac "SSR	rand.188	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "rand.188" "7" ltac_term:(G)) | idtac "SSR	rand.188	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.188" "8" ltac_term:(G)) | idtac "SSR	rand.188	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (length l + f 0 (snd (2, 0))) (S X)); elpi z_report "rand.188" "9" ltac_term:(G)) | idtac "SSR	rand.188	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in S X); elpi z_report "rand.188" "10" ltac_term:(G)) | idtac "SSR	rand.188	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.188" "11" ltac_term:(G)) | idtac "SSR	rand.188	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f _ (snd (S X, _))); elpi z_report "rand.188" "12" ltac_term:(G)) | idtac "SSR	rand.188	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst ((f (fst (c, 1)) ((a * 1) * (snd (0, c)))), ((fst ((snd (0, c)), (c + 3))) + 1))) 
= (fst (2, (snd ((a + 0), (length (l ++ l)))))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _); elpi z_report "rand.189" "1" ltac_term:(G)) | idtac "SSR	rand.189	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ _ as X in (2, snd (a + 0, length X))); elpi z_report "rand.189" "2" ltac_term:(G)) | idtac "SSR	rand.189	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ as X in (S _, snd (a + 0, length X))); elpi z_report "rand.189" "3" ltac_term:(G)) | idtac "SSR	rand.189	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ _ in X in fst X); elpi z_report "rand.189" "4" ltac_term:(G)) | idtac "SSR	rand.189	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (2, snd (_ + _, length X))); elpi z_report "rand.189" "5" ltac_term:(G)) | idtac "SSR	rand.189	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (2, snd (a + 0, length X))); elpi z_report "rand.189" "6" ltac_term:(G)) | idtac "SSR	rand.189	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (2, snd (_ + _, length X))); elpi z_report "rand.189" "7" ltac_term:(G)) | idtac "SSR	rand.189	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l ++ l in X in (a + 0, X)); elpi z_report "rand.189" "8" ltac_term:(G)) | idtac "SSR	rand.189	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in snd (a + _, length X)); elpi z_report "rand.189" "9" ltac_term:(G)) | idtac "SSR	rand.189	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ ++ l in X in fst (2, snd (_ + 0, X))); elpi z_report "rand.189" "10" ltac_term:(G)) | idtac "SSR	rand.189	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ ++ l in X in fst (2, X)); elpi z_report "rand.189" "11" ltac_term:(G)) | idtac "SSR	rand.189	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in fst (f (fst (c, 1)) (a * 1 * snd (0, c)), fst (snd (0, c), c + 3) + 1) = fst (_, snd (a + 0, length X))); elpi z_report "rand.189" "12" ltac_term:(G)) | idtac "SSR	rand.189	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(snd (3, ((snd ((length l), (f 2 c))) * a))) = (f 1 (g (g (g 3)))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in snd (3, snd (length l, f 2 c) * a) = f 1 (g (g (g (S X))))); elpi z_report "rand.190" "1" ltac_term:(G)) | idtac "SSR	rand.190	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (g (g (S (S X))))); elpi z_report "rand.190" "2" ltac_term:(G)) | idtac "SSR	rand.190	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X (g (g (g 3)))); elpi z_report "rand.190" "3" ltac_term:(G)) | idtac "SSR	rand.190	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (S (S X), snd (length l, f 2 c) * a)); elpi z_report "rand.190" "4" ltac_term:(G)) | idtac "SSR	rand.190	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in snd (3, snd (length l, f 2 c) * a) = f X (g (g (g 3)))); elpi z_report "rand.190" "5" ltac_term:(G)) | idtac "SSR	rand.190	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (S (S X), snd (length l, f 2 c) * a)); elpi z_report "rand.190" "6" ltac_term:(G)) | idtac "SSR	rand.190	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X)); elpi z_report "rand.190" "7" ltac_term:(G)) | idtac "SSR	rand.190	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (_, f (S X) c) * _); elpi z_report "rand.190" "8" ltac_term:(G)) | idtac "SSR	rand.190	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.190" "9" ltac_term:(G)) | idtac "SSR	rand.190	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f 1 (g X)); elpi z_report "rand.190" "10" ltac_term:(G)) | idtac "SSR	rand.190	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (S X, snd (length l, f 2 c) * a) = f 1 (g (g (g 3)))); elpi z_report "rand.190" "11" ltac_term:(G)) | idtac "SSR	rand.190	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in S X); elpi z_report "rand.190" "12" ltac_term:(G)) | idtac "SSR	rand.190	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (snd (c, (g (length (2 :: l))))) = 
(f (fst ((fst (c, (fst (3, 0)))), a)) (fst ((g (a + a)), (snd ((b * c), (fst (2, 3))))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in g (length (S X :: _))); elpi z_report "rand.191" "1" ltac_term:(G)) | idtac "SSR	rand.191	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (g (a + _), snd (_, fst (2, S X)))); elpi z_report "rand.191" "2" ltac_term:(G)) | idtac "SSR	rand.191	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (g (a + a), snd (b * c, fst (S X, 3)))); elpi z_report "rand.191" "3" ltac_term:(G)) | idtac "SSR	rand.191	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.191" "4" ltac_term:(G)) | idtac "SSR	rand.191	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in snd (c, g (length (2 :: l))) = f (fst (fst (c, fst (3, 0)), _)) (fst (g (a + a), snd (b * c, fst (S X, 3))))); elpi z_report "rand.191" "5" ltac_term:(G)) | idtac "SSR	rand.191	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.191" "6" ltac_term:(G)) | idtac "SSR	rand.191	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "rand.191" "7" ltac_term:(G)) | idtac "SSR	rand.191	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (fst (_, fst (S (S X), 0)), _)); elpi z_report "rand.191" "8" ltac_term:(G)) | idtac "SSR	rand.191	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.191" "9" ltac_term:(G)) | idtac "SSR	rand.191	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in fst (_, snd (_, fst (2, S (S X))))); elpi z_report "rand.191" "10" ltac_term:(G)) | idtac "SSR	rand.191	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in snd (c, g (length (S X :: _)))); elpi z_report "rand.191" "11" ltac_term:(G)) | idtac "SSR	rand.191	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (b * c, fst (X, S (S (S _))))); elpi z_report "rand.191" "12" ltac_term:(G)) | idtac "SSR	rand.191	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (length l) = 
((length ((length l) :: (l ++ l))) + 2) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length (length l :: l ++ l) + X); elpi z_report "rand.192" "1" ltac_term:(G)) | idtac "SSR	rand.192	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in length (length _ :: _ ++ _) + X); elpi z_report "rand.192" "2" ltac_term:(G)) | idtac "SSR	rand.192	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.192" "3" ltac_term:(G)) | idtac "SSR	rand.192	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in length (length l :: l ++ l) + S X); elpi z_report "rand.192" "4" ltac_term:(G)) | idtac "SSR	rand.192	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.192" "5" ltac_term:(G)) | idtac "SSR	rand.192	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length l = length (length l :: l ++ l) + S X); elpi z_report "rand.192" "6" ltac_term:(G)) | idtac "SSR	rand.192	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in length (length l :: l ++ l) + X); elpi z_report "rand.192" "7" ltac_term:(G)) | idtac "SSR	rand.192	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (length l :: l ++ l) + S X); elpi z_report "rand.192" "8" ltac_term:(G)) | idtac "SSR	rand.192	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (length l :: l ++ l) + S X); elpi z_report "rand.192" "9" ltac_term:(G)) | idtac "SSR	rand.192	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in length (length l :: l ++ l) + X); elpi z_report "rand.192" "10" ltac_term:(G)) | idtac "SSR	rand.192	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length l = X); elpi z_report "rand.192" "11" ltac_term:(G)) | idtac "SSR	rand.192	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "rand.192" "12" ltac_term:(G)) | idtac "SSR	rand.192	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
((fst (3, (f (length l) (c + 1)))) * (g (fst ((b * 3), (snd (a, 2)))))) = b .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst (3, f (length l) (c + 1)) * g (fst X) = b); elpi z_report "rand.193" "1" ltac_term:(G)) | idtac "SSR	rand.193	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (3, X)); elpi z_report "rand.193" "2" ltac_term:(G)) | idtac "SSR	rand.193	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in c + X); elpi z_report "rand.193" "3" ltac_term:(G)) | idtac "SSR	rand.193	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst (S X, f (length l) (c + S _)) * g (fst (b * 3, snd (a, 2)))); elpi z_report "rand.193" "4" ltac_term:(G)) | idtac "SSR	rand.193	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.193" "5" ltac_term:(G)) | idtac "SSR	rand.193	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.193" "6" ltac_term:(G)) | idtac "SSR	rand.193	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (3, f (length l) (c + X))); elpi z_report "rand.193" "7" ltac_term:(G)) | idtac "SSR	rand.193	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.193" "8" ltac_term:(G)) | idtac "SSR	rand.193	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in (_ * 3, snd (a, S X))); elpi z_report "rand.193" "9" ltac_term:(G)) | idtac "SSR	rand.193	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (3, f (length l) (c + 1)) * g (fst (b * 3, snd (_, S X))) = _); elpi z_report "rand.193" "10" ltac_term:(G)) | idtac "SSR	rand.193	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in fst (3, f (length l) (c + 1)) * g X = b); elpi z_report "rand.193" "11" ltac_term:(G)) | idtac "SSR	rand.193	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in (X, f (length l) (_ + 1))); elpi z_report "rand.193" "12" ltac_term:(G)) | idtac "SSR	rand.193	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), c = (b + (g 2)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S X)); elpi z_report "rand.194" "1" ltac_term:(G)) | idtac "SSR	rand.194	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g (S X)); elpi z_report "rand.194" "2" ltac_term:(G)) | idtac "SSR	rand.194	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.194" "3" ltac_term:(G)) | idtac "SSR	rand.194	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c = _ + g (S X)); elpi z_report "rand.194" "4" ltac_term:(G)) | idtac "SSR	rand.194	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b + g (S X)); elpi z_report "rand.194" "5" ltac_term:(G)) | idtac "SSR	rand.194	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S X)); elpi z_report "rand.194" "6" ltac_term:(G)) | idtac "SSR	rand.194	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in c = b + g X); elpi z_report "rand.194" "7" ltac_term:(G)) | idtac "SSR	rand.194	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (S X)); elpi z_report "rand.194" "8" ltac_term:(G)) | idtac "SSR	rand.194	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in c = _ + g (S X)); elpi z_report "rand.194" "9" ltac_term:(G)) | idtac "SSR	rand.194	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.194" "10" ltac_term:(G)) | idtac "SSR	rand.194	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (S X)); elpi z_report "rand.194" "11" ltac_term:(G)) | idtac "SSR	rand.194	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X); elpi z_report "rand.194" "12" ltac_term:(G)) | idtac "SSR	rand.194	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), (g 1) = 2 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g X); elpi z_report "rand.195" "1" ltac_term:(G)) | idtac "SSR	rand.195	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = 2); elpi z_report "rand.195" "2" ltac_term:(G)) | idtac "SSR	rand.195	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g X = 2); elpi z_report "rand.195" "3" ltac_term:(G)) | idtac "SSR	rand.195	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.195" "4" ltac_term:(G)) | idtac "SSR	rand.195	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.195" "5" ltac_term:(G)) | idtac "SSR	rand.195	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in g X = _); elpi z_report "rand.195" "6" ltac_term:(G)) | idtac "SSR	rand.195	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.195" "7" ltac_term:(G)) | idtac "SSR	rand.195	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S X); elpi z_report "rand.195" "8" ltac_term:(G)) | idtac "SSR	rand.195	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g X = 2); elpi z_report "rand.195" "9" ltac_term:(G)) | idtac "SSR	rand.195	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "rand.195" "10" ltac_term:(G)) | idtac "SSR	rand.195	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in g 1 = X); elpi z_report "rand.195" "11" ltac_term:(G)) | idtac "SSR	rand.195	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "rand.195" "12" ltac_term:(G)) | idtac "SSR	rand.195	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(fst (((f (0 + 0) 1) + (length (1 :: l))), c)) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f (0 + 0) 1 + length (1 :: l), c) = S (S X)); elpi z_report "rand.196" "1" ltac_term:(G)) | idtac "SSR	rand.196	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f (0 + 0) 1 + length (1 :: l), c) = S (S X)); elpi z_report "rand.196" "2" ltac_term:(G)) | idtac "SSR	rand.196	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in fst X); elpi z_report "rand.196" "3" ltac_term:(G)) | idtac "SSR	rand.196	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (0 + 0) 1 + length (X :: l)); elpi z_report "rand.196" "4" ltac_term:(G)) | idtac "SSR	rand.196	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in X :: l); elpi z_report "rand.196" "5" ltac_term:(G)) | idtac "SSR	rand.196	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.196" "6" ltac_term:(G)) | idtac "SSR	rand.196	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X = 3); elpi z_report "rand.196" "7" ltac_term:(G)) | idtac "SSR	rand.196	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S X); elpi z_report "rand.196" "8" ltac_term:(G)) | idtac "SSR	rand.196	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.196" "9" ltac_term:(G)) | idtac "SSR	rand.196	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (f (0 + 0) 1 + length (1 :: l), c) = S (S X)); elpi z_report "rand.196" "10" ltac_term:(G)) | idtac "SSR	rand.196	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X :: _); elpi z_report "rand.196" "11" ltac_term:(G)) | idtac "SSR	rand.196	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.196" "12" ltac_term:(G)) | idtac "SSR	rand.196	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = (length (1 :: l)) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in length (X :: _)); elpi z_report "rand.197" "1" ltac_term:(G)) | idtac "SSR	rand.197	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "rand.197" "2" ltac_term:(G)) | idtac "SSR	rand.197	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = length (1 :: l)); elpi z_report "rand.197" "3" ltac_term:(G)) | idtac "SSR	rand.197	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X = length (1 :: l)); elpi z_report "rand.197" "4" ltac_term:(G)) | idtac "SSR	rand.197	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length X); elpi z_report "rand.197" "5" ltac_term:(G)) | idtac "SSR	rand.197	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.197" "6" ltac_term:(G)) | idtac "SSR	rand.197	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.197" "7" ltac_term:(G)) | idtac "SSR	rand.197	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.197" "8" ltac_term:(G)) | idtac "SSR	rand.197	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (X :: _)); elpi z_report "rand.197" "9" ltac_term:(G)) | idtac "SSR	rand.197	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.197" "10" ltac_term:(G)) | idtac "SSR	rand.197	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S _ = length (X :: l)); elpi z_report "rand.197" "11" ltac_term:(G)) | idtac "SSR	rand.197	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = length (1 :: l)); elpi z_report "rand.197" "12" ltac_term:(G)) | idtac "SSR	rand.197	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), ((g c) * (length ((l ++ l) ++ l))) 
= 
(fst ((f ((g c) + (length l)) (f (a * b) (c * 3))), ((fst ((1 + 0), (snd (b, 2)))) * (snd (b, 3))))) 
.
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in snd (b, S X)); elpi z_report "rand.198" "1" ltac_term:(G)) | idtac "SSR	rand.198	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.198" "2" ltac_term:(G)) | idtac "SSR	rand.198	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (_, S (S X))); elpi z_report "rand.198" "3" ltac_term:(G)) | idtac "SSR	rand.198	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in f (g c + _) (f (a * b) (_ * S X))); elpi z_report "rand.198" "4" ltac_term:(G)) | idtac "SSR	rand.198	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in snd (_, S X)); elpi z_report "rand.198" "5" ltac_term:(G)) | idtac "SSR	rand.198	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in fst (X + 0, snd (b, 2))); elpi z_report "rand.198" "6" ltac_term:(G)) | idtac "SSR	rand.198	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in fst (f (g c + length l) (f (_ * b) (_ * 3)), fst (X + 0, snd (b, 2)) * snd (b, 3))); elpi z_report "rand.198" "7" ltac_term:(G)) | idtac "SSR	rand.198	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.198" "8" ltac_term:(G)) | idtac "SSR	rand.198	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in f (g c + length l) (f (_ * b) (c * S (S X)))); elpi z_report "rand.198" "9" ltac_term:(G)) | idtac "SSR	rand.198	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.198" "10" ltac_term:(G)) | idtac "SSR	rand.198	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in (X + _, snd (_, 2))); elpi z_report "rand.198" "11" ltac_term:(G)) | idtac "SSR	rand.198	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (f (g c + length l) (f (a * b) (c * 3)), fst (1 + 0, snd (b, 2)) * snd (_, X))); elpi z_report "rand.198" "12" ltac_term:(G)) | idtac "SSR	rand.198	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 1 = 
(((length (l ++ l)) + a) + ((fst ((g 3), (2 + a))) + (f 1 c))) .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (l ++ l) + a + (fst (g 3, 2 + a) + f X c)); elpi z_report "rand.199" "1" ltac_term:(G)) | idtac "SSR	rand.199	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in length (l ++ l) + a + (fst (g 3, 2 + a) + f X c)); elpi z_report "rand.199" "2" ltac_term:(G)) | idtac "SSR	rand.199	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S (S X)); elpi z_report "rand.199" "3" ltac_term:(G)) | idtac "SSR	rand.199	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in 1 = length (_ ++ l) + _ + (fst (g 3, 2 + a) + f X c)); elpi z_report "rand.199" "4" ltac_term:(G)) | idtac "SSR	rand.199	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in (X, 2 + a)); elpi z_report "rand.199" "5" ltac_term:(G)) | idtac "SSR	rand.199	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in 1 = length (l ++ l) + a + (fst (g 3, S X + a) + f 1 c)); elpi z_report "rand.199" "6" ltac_term:(G)) | idtac "SSR	rand.199	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.199" "7" ltac_term:(G)) | idtac "SSR	rand.199	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S _ = length (l ++ l) + a + (fst (g 3, 2 + a) + f X _)); elpi z_report "rand.199" "8" ltac_term:(G)) | idtac "SSR	rand.199	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in length (l ++ l) + _ + (fst (g 3, X + a) + f _ _)); elpi z_report "rand.199" "9" ltac_term:(G)) | idtac "SSR	rand.199	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in length (l ++ l) + a + (fst (g (S (S X)), 2 + _) + f 1 c)); elpi z_report "rand.199" "10" ltac_term:(G)) | idtac "SSR	rand.199	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in S (S X)); elpi z_report "rand.199" "11" ltac_term:(G)) | idtac "SSR	rand.199	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.199" "12" ltac_term:(G)) | idtac "SSR	rand.199	12	error" ].
Abort.

Goal forall (a b c : nat) (l : list nat), 
(g (1 + (snd ((snd (c, c)), (snd (c, 2)))))) = 3 .
intros a b c l.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in g (1 + snd (snd (_, c), snd (c, S X))) = 3); elpi z_report "rand.200" "1" ltac_term:(G)) | idtac "SSR	rand.200	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in (_, S X)); elpi z_report "rand.200" "2" ltac_term:(G)) | idtac "SSR	rand.200	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S X); elpi z_report "rand.200" "3" ltac_term:(G)) | idtac "SSR	rand.200	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in g (X + snd (snd (c, c), snd (c, 2))) = 3); elpi z_report "rand.200" "4" ltac_term:(G)) | idtac "SSR	rand.200	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + snd (snd (c, _), snd (c, 2))); elpi z_report "rand.200" "5" ltac_term:(G)) | idtac "SSR	rand.200	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in S X); elpi z_report "rand.200" "6" ltac_term:(G)) | idtac "SSR	rand.200	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "rand.200" "7" ltac_term:(G)) | idtac "SSR	rand.200	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "rand.200" "8" ltac_term:(G)) | idtac "SSR	rand.200	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in g X); elpi z_report "rand.200" "9" ltac_term:(G)) | idtac "SSR	rand.200	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "rand.200" "10" ltac_term:(G)) | idtac "SSR	rand.200	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + snd (snd (c, c), snd (_, S X))); elpi z_report "rand.200" "11" ltac_term:(G)) | idtac "SSR	rand.200	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "rand.200" "12" ltac_term:(G)) | idtac "SSR	rand.200	12	error" ].
Abort.

End Random.
