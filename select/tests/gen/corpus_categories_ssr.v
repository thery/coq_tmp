(* Differential corpus by category: each Id is <category>.<n>; run.sh
   counts the cases per category.  Each goal also gets the patterns of
   select_all and point_to_pattern (diff_gen). *)
From Stdlib Require Import List.
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support.
Import ListNotations.

(* forms: t, X in C, t in X in C, t as X in C, {k}, {k1 k2}, {-k} *)
Goal forall (f : nat -> nat -> nat) a b c, f (a + b) (b + c) = f (a + b) (c + b) + (a + b).
intros f a b c.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + b); elpi z_report "forms.1" "1" ltac_term:(G)) | idtac "SSR	forms.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X _); elpi z_report "forms.1" "2" ltac_term:(G)) | idtac "SSR	forms.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ X); elpi z_report "forms.1" "3" ltac_term:(G)) | idtac "SSR	forms.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in f _ X); elpi z_report "forms.1" "4" ltac_term:(G)) | idtac "SSR	forms.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + b as X in f _ X); elpi z_report "forms.1" "5" ltac_term:(G)) | idtac "SSR	forms.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + b); elpi z_report "forms.1" "6" ltac_term:(G)) | idtac "SSR	forms.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + b); elpi z_report "forms.1" "7" ltac_term:(G)) | idtac "SSR	forms.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1 3}(_ + b); elpi z_report "forms.1" "8" ltac_term:(G)) | idtac "SSR	forms.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {-1}(_ + b); elpi z_report "forms.1" "9" ltac_term:(G)) | idtac "SSR	forms.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {-2 3}(_ + b); elpi z_report "forms.1" "10" ltac_term:(G)) | idtac "SSR	forms.1	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(_ + b); elpi z_report "forms.1" "11" ltac_term:(G)) | idtac "SSR	forms.1	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in f X _); elpi z_report "forms.1" "12" ltac_term:(G)) | idtac "SSR	forms.1	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _ in X in f _ X); elpi z_report "forms.1" "13" ltac_term:(G)) | idtac "SSR	forms.1	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + b); elpi z_report "forms.1" "14" ltac_term:(G)) | idtac "SSR	forms.1	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a + b); elpi z_report "forms.1" "15" ltac_term:(G)) | idtac "SSR	forms.1	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "forms.1" "16" ltac_term:(G)) | idtac "SSR	forms.1	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _ in X in _ = X); elpi z_report "forms.1" "17" ltac_term:(G)) | idtac "SSR	forms.1	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ X + _); elpi z_report "forms.1" "18" ltac_term:(G)) | idtac "SSR	forms.1	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "forms.1g" "1" ltac_term:(G)) | idtac "SSR	forms.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (a + b) (b + c) = f (a + b) (c + b) + (a + b)); elpi z_report "forms.1g" "2" ltac_term:(G)) | idtac "SSR	forms.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "forms.1g" "3" ltac_term:(G)) | idtac "SSR	forms.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "forms.1g" "4" ltac_term:(G)) | idtac "SSR	forms.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "forms.1g" "5" ltac_term:(G)) | idtac "SSR	forms.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "forms.1g" "6" ltac_term:(G)) | idtac "SSR	forms.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _); elpi z_report "forms.1g" "7" ltac_term:(G)) | idtac "SSR	forms.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "forms.1g" "8" ltac_term:(G)) | idtac "SSR	forms.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _ as X in X = _); elpi z_report "forms.1g" "9" ltac_term:(G)) | idtac "SSR	forms.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (a + b) (b + c)); elpi z_report "forms.1g" "10" ltac_term:(G)) | idtac "SSR	forms.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f); elpi z_report "forms.1g" "11" ltac_term:(G)) | idtac "SSR	forms.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f); elpi z_report "forms.1g" "12" ltac_term:(G)) | idtac "SSR	forms.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X _); elpi z_report "forms.1g" "13" ltac_term:(G)) | idtac "SSR	forms.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X _); elpi z_report "forms.1g" "14" ltac_term:(G)) | idtac "SSR	forms.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X = _); elpi z_report "forms.1g" "15" ltac_term:(G)) | idtac "SSR	forms.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X _ = _); elpi z_report "forms.1g" "16" ltac_term:(G)) | idtac "SSR	forms.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X _ = _); elpi z_report "forms.1g" "17" ltac_term:(G)) | idtac "SSR	forms.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "forms.1g" "18" ltac_term:(G)) | idtac "SSR	forms.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _); elpi z_report "forms.1g" "19" ltac_term:(G)) | idtac "SSR	forms.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "forms.1g" "20" ltac_term:(G)) | idtac "SSR	forms.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "forms.1g" "21" ltac_term:(G)) | idtac "SSR	forms.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "forms.1g" "22" ltac_term:(G)) | idtac "SSR	forms.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X + _) _); elpi z_report "forms.1g" "23" ltac_term:(G)) | idtac "SSR	forms.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X + _) _ = _); elpi z_report "forms.1g" "24" ltac_term:(G)) | idtac "SSR	forms.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "forms.1g" "25" ltac_term:(G)) | idtac "SSR	forms.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "forms.1g" "26" ltac_term:(G)) | idtac "SSR	forms.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "forms.1g" "27" ltac_term:(G)) | idtac "SSR	forms.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + _); elpi z_report "forms.1g" "28" ltac_term:(G)) | idtac "SSR	forms.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X) _); elpi z_report "forms.1g" "29" ltac_term:(G)) | idtac "SSR	forms.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X) _ = _); elpi z_report "forms.1g" "30" ltac_term:(G)) | idtac "SSR	forms.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "forms.1g" "31" ltac_term:(G)) | idtac "SSR	forms.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "forms.1g" "32" ltac_term:(G)) | idtac "SSR	forms.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "forms.1g" "33" ltac_term:(G)) | idtac "SSR	forms.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ + X); elpi z_report "forms.1g" "34" ltac_term:(G)) | idtac "SSR	forms.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ X); elpi z_report "forms.1g" "35" ltac_term:(G)) | idtac "SSR	forms.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _); elpi z_report "forms.1g" "36" ltac_term:(G)) | idtac "SSR	forms.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f _ X); elpi z_report "forms.1g" "37" ltac_term:(G)) | idtac "SSR	forms.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ X = _); elpi z_report "forms.1g" "38" ltac_term:(G)) | idtac "SSR	forms.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _ in X in X = _); elpi z_report "forms.1g" "39" ltac_term:(G)) | idtac "SSR	forms.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f _ X = _); elpi z_report "forms.1g" "40" ltac_term:(G)) | idtac "SSR	forms.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b + c); elpi z_report "forms.1g" "41" ltac_term:(G)) | idtac "SSR	forms.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "forms.1g" "42" ltac_term:(G)) | idtac "SSR	forms.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "forms.1g" "43" ltac_term:(G)) | idtac "SSR	forms.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + c); elpi z_report "forms.1g" "44" ltac_term:(G)) | idtac "SSR	forms.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (X + _)); elpi z_report "forms.1g" "45" ltac_term:(G)) | idtac "SSR	forms.1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (X + _) = _); elpi z_report "forms.1g" "46" ltac_term:(G)) | idtac "SSR	forms.1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "forms.1g" "47" ltac_term:(G)) | idtac "SSR	forms.1g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "forms.1g" "48" ltac_term:(G)) | idtac "SSR	forms.1g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b + X); elpi z_report "forms.1g" "49" ltac_term:(G)) | idtac "SSR	forms.1g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (_ + X)); elpi z_report "forms.1g" "50" ltac_term:(G)) | idtac "SSR	forms.1g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (_ + X) = _); elpi z_report "forms.1g" "51" ltac_term:(G)) | idtac "SSR	forms.1g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "forms.1g" "52" ltac_term:(G)) | idtac "SSR	forms.1g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "forms.1g" "53" ltac_term:(G)) | idtac "SSR	forms.1g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "forms.1g" "54" ltac_term:(G)) | idtac "SSR	forms.1g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "forms.1g" "55" ltac_term:(G)) | idtac "SSR	forms.1g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (a + b)); elpi z_report "forms.1g" "56" ltac_term:(G)) | idtac "SSR	forms.1g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (a + b) (c + b) + (a + b)); elpi z_report "forms.1g" "57" ltac_term:(G)) | idtac "SSR	forms.1g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "forms.1g" "58" ltac_term:(G)) | idtac "SSR	forms.1g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "forms.1g" "59" ltac_term:(G)) | idtac "SSR	forms.1g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _ as X in X + _); elpi z_report "forms.1g" "60" ltac_term:(G)) | idtac "SSR	forms.1g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _ in X in _ = X); elpi z_report "forms.1g" "61" ltac_term:(G)) | idtac "SSR	forms.1g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "forms.1g" "62" ltac_term:(G)) | idtac "SSR	forms.1g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ (c + _)); elpi z_report "forms.1g" "63" ltac_term:(G)) | idtac "SSR	forms.1g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ _ as X in _ = X + _); elpi z_report "forms.1g" "64" ltac_term:(G)) | idtac "SSR	forms.1g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (a + b)); elpi z_report "forms.1g" "65" ltac_term:(G)) | idtac "SSR	forms.1g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (a + b) (c + b)); elpi z_report "forms.1g" "66" ltac_term:(G)) | idtac "SSR	forms.1g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f); elpi z_report "forms.1g" "67" ltac_term:(G)) | idtac "SSR	forms.1g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(f); elpi z_report "forms.1g" "68" ltac_term:(G)) | idtac "SSR	forms.1g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(f); elpi z_report "forms.1g" "69" ltac_term:(G)) | idtac "SSR	forms.1g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X _ + _); elpi z_report "forms.1g" "70" ltac_term:(G)) | idtac "SSR	forms.1g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X (c + _)); elpi z_report "forms.1g" "71" ltac_term:(G)) | idtac "SSR	forms.1g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X _ + _); elpi z_report "forms.1g" "72" ltac_term:(G)) | idtac "SSR	forms.1g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ = X + _); elpi z_report "forms.1g" "73" ltac_term:(G)) | idtac "SSR	forms.1g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f X _ + _); elpi z_report "forms.1g" "74" ltac_term:(G)) | idtac "SSR	forms.1g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X (c + _)); elpi z_report "forms.1g" "75" ltac_term:(G)) | idtac "SSR	forms.1g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = f X _ + _); elpi z_report "forms.1g" "76" ltac_term:(G)) | idtac "SSR	forms.1g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X + (a + b)); elpi z_report "forms.1g" "77" ltac_term:(G)) | idtac "SSR	forms.1g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + _); elpi z_report "forms.1g" "78" ltac_term:(G)) | idtac "SSR	forms.1g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + b); elpi z_report "forms.1g" "79" ltac_term:(G)) | idtac "SSR	forms.1g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + _ in X in _ = X); elpi z_report "forms.1g" "80" ltac_term:(G)) | idtac "SSR	forms.1g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "forms.1g" "81" ltac_term:(G)) | idtac "SSR	forms.1g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "forms.1g" "82" ltac_term:(G)) | idtac "SSR	forms.1g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X + _) _ + _); elpi z_report "forms.1g" "83" ltac_term:(G)) | idtac "SSR	forms.1g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X + _) (c + _)); elpi z_report "forms.1g" "84" ltac_term:(G)) | idtac "SSR	forms.1g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (X + _) _ + _); elpi z_report "forms.1g" "85" ltac_term:(G)) | idtac "SSR	forms.1g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + b); elpi z_report "forms.1g" "86" ltac_term:(G)) | idtac "SSR	forms.1g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "forms.1g" "87" ltac_term:(G)) | idtac "SSR	forms.1g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "forms.1g" "88" ltac_term:(G)) | idtac "SSR	forms.1g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X + b); elpi z_report "forms.1g" "89" ltac_term:(G)) | idtac "SSR	forms.1g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X) _ + _); elpi z_report "forms.1g" "90" ltac_term:(G)) | idtac "SSR	forms.1g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X) (c + _)); elpi z_report "forms.1g" "91" ltac_term:(G)) | idtac "SSR	forms.1g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (_ + X) _ + _); elpi z_report "forms.1g" "92" ltac_term:(G)) | idtac "SSR	forms.1g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "forms.1g" "93" ltac_term:(G)) | idtac "SSR	forms.1g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "forms.1g" "94" ltac_term:(G)) | idtac "SSR	forms.1g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in a + X); elpi z_report "forms.1g" "95" ltac_term:(G)) | idtac "SSR	forms.1g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _); elpi z_report "forms.1g" "96" ltac_term:(G)) | idtac "SSR	forms.1g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ X + _); elpi z_report "forms.1g" "97" ltac_term:(G)) | idtac "SSR	forms.1g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _ as X in f _ X); elpi z_report "forms.1g" "98" ltac_term:(G)) | idtac "SSR	forms.1g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _ in X in _ = X); elpi z_report "forms.1g" "99" ltac_term:(G)) | idtac "SSR	forms.1g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f _ X + _); elpi z_report "forms.1g" "100" ltac_term:(G)) | idtac "SSR	forms.1g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f _ X + _); elpi z_report "forms.1g" "101" ltac_term:(G)) | idtac "SSR	forms.1g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _ in X in _ = X + _); elpi z_report "forms.1g" "102" ltac_term:(G)) | idtac "SSR	forms.1g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = f _ X + _); elpi z_report "forms.1g" "103" ltac_term:(G)) | idtac "SSR	forms.1g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _ in X in X + (a + b)); elpi z_report "forms.1g" "104" ltac_term:(G)) | idtac "SSR	forms.1g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c + b); elpi z_report "forms.1g" "105" ltac_term:(G)) | idtac "SSR	forms.1g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Nat.add); elpi z_report "forms.1g" "106" ltac_term:(G)) | idtac "SSR	forms.1g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Nat.add); elpi z_report "forms.1g" "107" ltac_term:(G)) | idtac "SSR	forms.1g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (X + b)); elpi z_report "forms.1g" "108" ltac_term:(G)) | idtac "SSR	forms.1g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (X + _) + _); elpi z_report "forms.1g" "109" ltac_term:(G)) | idtac "SSR	forms.1g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f _ (X + _) + _); elpi z_report "forms.1g" "110" ltac_term:(G)) | idtac "SSR	forms.1g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "forms.1g" "111" ltac_term:(G)) | idtac "SSR	forms.1g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "forms.1g" "112" ltac_term:(G)) | idtac "SSR	forms.1g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "forms.1g" "113" ltac_term:(G)) | idtac "SSR	forms.1g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c + X); elpi z_report "forms.1g" "114" ltac_term:(G)) | idtac "SSR	forms.1g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (c + X)); elpi z_report "forms.1g" "115" ltac_term:(G)) | idtac "SSR	forms.1g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f _ (_ + X) + _); elpi z_report "forms.1g" "116" ltac_term:(G)) | idtac "SSR	forms.1g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f _ (_ + X) + _); elpi z_report "forms.1g" "117" ltac_term:(G)) | idtac "SSR	forms.1g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(b); elpi z_report "forms.1g" "118" ltac_term:(G)) | idtac "SSR	forms.1g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(b); elpi z_report "forms.1g" "119" ltac_term:(G)) | idtac "SSR	forms.1g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "forms.1g" "120" ltac_term:(G)) | idtac "SSR	forms.1g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "forms.1g" "121" ltac_term:(G)) | idtac "SSR	forms.1g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = _ + X); elpi z_report "forms.1g" "122" ltac_term:(G)) | idtac "SSR	forms.1g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (a + b) (c + b) + X); elpi z_report "forms.1g" "123" ltac_term:(G)) | idtac "SSR	forms.1g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "forms.1g" "124" ltac_term:(G)) | idtac "SSR	forms.1g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in _ = X); elpi z_report "forms.1g" "125" ltac_term:(G)) | idtac "SSR	forms.1g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a + _); elpi z_report "forms.1g" "126" ltac_term:(G)) | idtac "SSR	forms.1g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a + b); elpi z_report "forms.1g" "127" ltac_term:(G)) | idtac "SSR	forms.1g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + _ in X in _ = X); elpi z_report "forms.1g" "128" ltac_term:(G)) | idtac "SSR	forms.1g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "forms.1g" "129" ltac_term:(G)) | idtac "SSR	forms.1g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(Nat.add); elpi z_report "forms.1g" "130" ltac_term:(G)) | idtac "SSR	forms.1g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(Nat.add); elpi z_report "forms.1g" "131" ltac_term:(G)) | idtac "SSR	forms.1g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "forms.1g" "132" ltac_term:(G)) | idtac "SSR	forms.1g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (X + _)); elpi z_report "forms.1g" "133" ltac_term:(G)) | idtac "SSR	forms.1g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "forms.1g" "134" ltac_term:(G)) | idtac "SSR	forms.1g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "forms.1g" "135" ltac_term:(G)) | idtac "SSR	forms.1g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "forms.1g" "136" ltac_term:(G)) | idtac "SSR	forms.1g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "forms.1g" "137" ltac_term:(G)) | idtac "SSR	forms.1g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ + X)); elpi z_report "forms.1g" "138" ltac_term:(G)) | idtac "SSR	forms.1g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "forms.1g" "139" ltac_term:(G)) | idtac "SSR	forms.1g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + X); elpi z_report "forms.1g" "140" ltac_term:(G)) | idtac "SSR	forms.1g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(b); elpi z_report "forms.1g" "141" ltac_term:(G)) | idtac "SSR	forms.1g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(b); elpi z_report "forms.1g" "142" ltac_term:(G)) | idtac "SSR	forms.1g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in a + X); elpi z_report "forms.1g" "143" ltac_term:(G)) | idtac "SSR	forms.1g	143	error" ].
Abort.

(* pre-order: an ancestor before its descendants, left before right,
   nested applications of the same key *)
Goal forall a b c : nat, (a + b) + c = a + (b + c) /\ (a * b) * (a * b) = 0.
intros a b c.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "order.1" "1" ltac_term:(G)) | idtac "SSR	order.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + c); elpi z_report "order.1" "2" ltac_term:(G)) | idtac "SSR	order.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "order.1" "3" ltac_term:(G)) | idtac "SSR	order.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (_ + _)); elpi z_report "order.1" "4" ltac_term:(G)) | idtac "SSR	order.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_ + _) + _); elpi z_report "order.1" "5" ltac_term:(G)) | idtac "SSR	order.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "order.1" "6" ltac_term:(G)) | idtac "SSR	order.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a * _); elpi z_report "order.1" "7" ltac_term:(G)) | idtac "SSR	order.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "order.1" "8" ltac_term:(G)) | idtac "SSR	order.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "order.1" "9" ltac_term:(G)) | idtac "SSR	order.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ * _); elpi z_report "order.1" "10" ltac_term:(G)) | idtac "SSR	order.1	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "order.1" "11" ltac_term:(G)) | idtac "SSR	order.1	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ = _); elpi z_report "order.1" "12" ltac_term:(G)) | idtac "SSR	order.1	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "order.1" "13" ltac_term:(G)) | idtac "SSR	order.1	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "order.1" "14" ltac_term:(G)) | idtac "SSR	order.1	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "order.1" "15" ltac_term:(G)) | idtac "SSR	order.1	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "order.1g" "1" ltac_term:(G)) | idtac "SSR	order.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b + c = a + (b + c) /\ a * b * (a * b) = 0); elpi z_report "order.1g" "2" ltac_term:(G)) | idtac "SSR	order.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "order.1g" "3" ltac_term:(G)) | idtac "SSR	order.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "order.1g" "4" ltac_term:(G)) | idtac "SSR	order.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "order.1g" "5" ltac_term:(G)) | idtac "SSR	order.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "order.1g" "6" ltac_term:(G)) | idtac "SSR	order.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "order.1g" "7" ltac_term:(G)) | idtac "SSR	order.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b + c = a + (b + c)); elpi z_report "order.1g" "8" ltac_term:(G)) | idtac "SSR	order.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "order.1g" "9" ltac_term:(G)) | idtac "SSR	order.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "order.1g" "10" ltac_term:(G)) | idtac "SSR	order.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "order.1g" "11" ltac_term:(G)) | idtac "SSR	order.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "order.1g" "12" ltac_term:(G)) | idtac "SSR	order.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "order.1g" "13" ltac_term:(G)) | idtac "SSR	order.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "order.1g" "14" ltac_term:(G)) | idtac "SSR	order.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "order.1g" "15" ltac_term:(G)) | idtac "SSR	order.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ _); elpi z_report "order.1g" "16" ltac_term:(G)) | idtac "SSR	order.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "order.1g" "17" ltac_term:(G)) | idtac "SSR	order.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _ /\ _); elpi z_report "order.1g" "18" ltac_term:(G)) | idtac "SSR	order.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b + c); elpi z_report "order.1g" "19" ltac_term:(G)) | idtac "SSR	order.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "order.1g" "20" ltac_term:(G)) | idtac "SSR	order.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "order.1g" "21" ltac_term:(G)) | idtac "SSR	order.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "order.1g" "22" ltac_term:(G)) | idtac "SSR	order.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "order.1g" "23" ltac_term:(G)) | idtac "SSR	order.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "order.1g" "24" ltac_term:(G)) | idtac "SSR	order.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "order.1g" "25" ltac_term:(G)) | idtac "SSR	order.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X = _); elpi z_report "order.1g" "26" ltac_term:(G)) | idtac "SSR	order.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X /\ _); elpi z_report "order.1g" "27" ltac_term:(G)) | idtac "SSR	order.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "order.1g" "28" ltac_term:(G)) | idtac "SSR	order.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _ /\ _); elpi z_report "order.1g" "29" ltac_term:(G)) | idtac "SSR	order.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X = _ /\ _); elpi z_report "order.1g" "30" ltac_term:(G)) | idtac "SSR	order.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _ /\ _); elpi z_report "order.1g" "31" ltac_term:(G)) | idtac "SSR	order.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "order.1g" "32" ltac_term:(G)) | idtac "SSR	order.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "order.1g" "33" ltac_term:(G)) | idtac "SSR	order.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "order.1g" "34" ltac_term:(G)) | idtac "SSR	order.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + b); elpi z_report "order.1g" "35" ltac_term:(G)) | idtac "SSR	order.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "order.1g" "36" ltac_term:(G)) | idtac "SSR	order.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "order.1g" "37" ltac_term:(G)) | idtac "SSR	order.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _ /\ _); elpi z_report "order.1g" "38" ltac_term:(G)) | idtac "SSR	order.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "order.1g" "39" ltac_term:(G)) | idtac "SSR	order.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "order.1g" "40" ltac_term:(G)) | idtac "SSR	order.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + X); elpi z_report "order.1g" "41" ltac_term:(G)) | idtac "SSR	order.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "order.1g" "42" ltac_term:(G)) | idtac "SSR	order.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "order.1g" "43" ltac_term:(G)) | idtac "SSR	order.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _ /\ _); elpi z_report "order.1g" "44" ltac_term:(G)) | idtac "SSR	order.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "order.1g" "45" ltac_term:(G)) | idtac "SSR	order.1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "order.1g" "46" ltac_term:(G)) | idtac "SSR	order.1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "order.1g" "47" ltac_term:(G)) | idtac "SSR	order.1g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "order.1g" "48" ltac_term:(G)) | idtac "SSR	order.1g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _ /\ _); elpi z_report "order.1g" "49" ltac_term:(G)) | idtac "SSR	order.1g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "order.1g" "50" ltac_term:(G)) | idtac "SSR	order.1g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "order.1g" "51" ltac_term:(G)) | idtac "SSR	order.1g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "order.1g" "52" ltac_term:(G)) | idtac "SSR	order.1g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "order.1g" "53" ltac_term:(G)) | idtac "SSR	order.1g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "order.1g" "54" ltac_term:(G)) | idtac "SSR	order.1g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X /\ _); elpi z_report "order.1g" "55" ltac_term:(G)) | idtac "SSR	order.1g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (b + c)); elpi z_report "order.1g" "56" ltac_term:(G)) | idtac "SSR	order.1g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (b + c) in X in X /\ _); elpi z_report "order.1g" "57" ltac_term:(G)) | idtac "SSR	order.1g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + (b + c)); elpi z_report "order.1g" "58" ltac_term:(G)) | idtac "SSR	order.1g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "order.1g" "59" ltac_term:(G)) | idtac "SSR	order.1g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "order.1g" "60" ltac_term:(G)) | idtac "SSR	order.1g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "order.1g" "61" ltac_term:(G)) | idtac "SSR	order.1g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ /\ _); elpi z_report "order.1g" "62" ltac_term:(G)) | idtac "SSR	order.1g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (b + c)); elpi z_report "order.1g" "63" ltac_term:(G)) | idtac "SSR	order.1g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "order.1g" "64" ltac_term:(G)) | idtac "SSR	order.1g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "order.1g" "65" ltac_term:(G)) | idtac "SSR	order.1g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _); elpi z_report "order.1g" "66" ltac_term:(G)) | idtac "SSR	order.1g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "order.1g" "67" ltac_term:(G)) | idtac "SSR	order.1g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "order.1g" "68" ltac_term:(G)) | idtac "SSR	order.1g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _ in X in _ = X); elpi z_report "order.1g" "69" ltac_term:(G)) | idtac "SSR	order.1g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _ in X in X /\ _); elpi z_report "order.1g" "70" ltac_term:(G)) | idtac "SSR	order.1g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = _ + X); elpi z_report "order.1g" "71" ltac_term:(G)) | idtac "SSR	order.1g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X /\ _); elpi z_report "order.1g" "72" ltac_term:(G)) | idtac "SSR	order.1g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _ in X in _ = X /\ _); elpi z_report "order.1g" "73" ltac_term:(G)) | idtac "SSR	order.1g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = _ + X /\ _); elpi z_report "order.1g" "74" ltac_term:(G)) | idtac "SSR	order.1g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b + c); elpi z_report "order.1g" "75" ltac_term:(G)) | idtac "SSR	order.1g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "order.1g" "76" ltac_term:(G)) | idtac "SSR	order.1g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "order.1g" "77" ltac_term:(G)) | idtac "SSR	order.1g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "order.1g" "78" ltac_term:(G)) | idtac "SSR	order.1g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "order.1g" "79" ltac_term:(G)) | idtac "SSR	order.1g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (X + _)); elpi z_report "order.1g" "80" ltac_term:(G)) | idtac "SSR	order.1g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (X + _) /\ _); elpi z_report "order.1g" "81" ltac_term:(G)) | idtac "SSR	order.1g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "order.1g" "82" ltac_term:(G)) | idtac "SSR	order.1g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "order.1g" "83" ltac_term:(G)) | idtac "SSR	order.1g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b + X); elpi z_report "order.1g" "84" ltac_term:(G)) | idtac "SSR	order.1g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "order.1g" "85" ltac_term:(G)) | idtac "SSR	order.1g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ + X)); elpi z_report "order.1g" "86" ltac_term:(G)) | idtac "SSR	order.1g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ + X) /\ _); elpi z_report "order.1g" "87" ltac_term:(G)) | idtac "SSR	order.1g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "order.1g" "88" ltac_term:(G)) | idtac "SSR	order.1g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "order.1g" "89" ltac_term:(G)) | idtac "SSR	order.1g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "order.1g" "90" ltac_term:(G)) | idtac "SSR	order.1g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "order.1g" "91" ltac_term:(G)) | idtac "SSR	order.1g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = 0); elpi z_report "order.1g" "92" ltac_term:(G)) | idtac "SSR	order.1g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "order.1g" "93" ltac_term:(G)) | idtac "SSR	order.1g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * b * (a * b) = 0); elpi z_report "order.1g" "94" ltac_term:(G)) | idtac "SSR	order.1g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "order.1g" "95" ltac_term:(G)) | idtac "SSR	order.1g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "order.1g" "96" ltac_term:(G)) | idtac "SSR	order.1g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "order.1g" "97" ltac_term:(G)) | idtac "SSR	order.1g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "order.1g" "98" ltac_term:(G)) | idtac "SSR	order.1g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "order.1g" "99" ltac_term:(G)) | idtac "SSR	order.1g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "order.1g" "100" ltac_term:(G)) | idtac "SSR	order.1g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "order.1g" "101" ltac_term:(G)) | idtac "SSR	order.1g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = 0); elpi z_report "order.1g" "102" ltac_term:(G)) | idtac "SSR	order.1g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in X = _); elpi z_report "order.1g" "103" ltac_term:(G)) | idtac "SSR	order.1g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ /\ X); elpi z_report "order.1g" "104" ltac_term:(G)) | idtac "SSR	order.1g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "order.1g" "105" ltac_term:(G)) | idtac "SSR	order.1g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ /\ X = _); elpi z_report "order.1g" "106" ltac_term:(G)) | idtac "SSR	order.1g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * b * (a * b)); elpi z_report "order.1g" "107" ltac_term:(G)) | idtac "SSR	order.1g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.mul); elpi z_report "order.1g" "108" ltac_term:(G)) | idtac "SSR	order.1g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.mul); elpi z_report "order.1g" "109" ltac_term:(G)) | idtac "SSR	order.1g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "order.1g" "110" ltac_term:(G)) | idtac "SSR	order.1g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in X * _); elpi z_report "order.1g" "111" ltac_term:(G)) | idtac "SSR	order.1g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _ = _); elpi z_report "order.1g" "112" ltac_term:(G)) | idtac "SSR	order.1g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in X * _ = _); elpi z_report "order.1g" "113" ltac_term:(G)) | idtac "SSR	order.1g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X * _ = _); elpi z_report "order.1g" "114" ltac_term:(G)) | idtac "SSR	order.1g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ /\ X * _ = _); elpi z_report "order.1g" "115" ltac_term:(G)) | idtac "SSR	order.1g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * _); elpi z_report "order.1g" "116" ltac_term:(G)) | idtac "SSR	order.1g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * b); elpi z_report "order.1g" "117" ltac_term:(G)) | idtac "SSR	order.1g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * _ in X in _ /\ X); elpi z_report "order.1g" "118" ltac_term:(G)) | idtac "SSR	order.1g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * _ in X in X = 0); elpi z_report "order.1g" "119" ltac_term:(G)) | idtac "SSR	order.1g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * _ in X in _ /\ X = _); elpi z_report "order.1g" "120" ltac_term:(G)) | idtac "SSR	order.1g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.mul); elpi z_report "order.1g" "121" ltac_term:(G)) | idtac "SSR	order.1g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.mul); elpi z_report "order.1g" "122" ltac_term:(G)) | idtac "SSR	order.1g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _ * _); elpi z_report "order.1g" "123" ltac_term:(G)) | idtac "SSR	order.1g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _ * _ = _); elpi z_report "order.1g" "124" ltac_term:(G)) | idtac "SSR	order.1g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X * _ * _ = _); elpi z_report "order.1g" "125" ltac_term:(G)) | idtac "SSR	order.1g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "order.1g" "126" ltac_term:(G)) | idtac "SSR	order.1g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "order.1g" "127" ltac_term:(G)) | idtac "SSR	order.1g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X * b); elpi z_report "order.1g" "128" ltac_term:(G)) | idtac "SSR	order.1g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X * _); elpi z_report "order.1g" "129" ltac_term:(G)) | idtac "SSR	order.1g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X * _ = _); elpi z_report "order.1g" "130" ltac_term:(G)) | idtac "SSR	order.1g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ * X * _ = _); elpi z_report "order.1g" "131" ltac_term:(G)) | idtac "SSR	order.1g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "order.1g" "132" ltac_term:(G)) | idtac "SSR	order.1g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "order.1g" "133" ltac_term:(G)) | idtac "SSR	order.1g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in a * X); elpi z_report "order.1g" "134" ltac_term:(G)) | idtac "SSR	order.1g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "order.1g" "135" ltac_term:(G)) | idtac "SSR	order.1g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ * X); elpi z_report "order.1g" "136" ltac_term:(G)) | idtac "SSR	order.1g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X = _); elpi z_report "order.1g" "137" ltac_term:(G)) | idtac "SSR	order.1g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ * X = _); elpi z_report "order.1g" "138" ltac_term:(G)) | idtac "SSR	order.1g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ * X = _); elpi z_report "order.1g" "139" ltac_term:(G)) | idtac "SSR	order.1g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ /\ _ * X = _); elpi z_report "order.1g" "140" ltac_term:(G)) | idtac "SSR	order.1g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a * _); elpi z_report "order.1g" "141" ltac_term:(G)) | idtac "SSR	order.1g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a * _ in X in _ /\ X); elpi z_report "order.1g" "142" ltac_term:(G)) | idtac "SSR	order.1g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a * _ in X in X = 0); elpi z_report "order.1g" "143" ltac_term:(G)) | idtac "SSR	order.1g	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a * _ in X in _ /\ X = _); elpi z_report "order.1g" "144" ltac_term:(G)) | idtac "SSR	order.1g	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a * _); elpi z_report "order.1g" "145" ltac_term:(G)) | idtac "SSR	order.1g	145	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a * b); elpi z_report "order.1g" "146" ltac_term:(G)) | idtac "SSR	order.1g	146	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a * _ in X in _ /\ X); elpi z_report "order.1g" "147" ltac_term:(G)) | idtac "SSR	order.1g	147	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a * _ in X in X = 0); elpi z_report "order.1g" "148" ltac_term:(G)) | idtac "SSR	order.1g	148	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a * _ in X in _ /\ X = _); elpi z_report "order.1g" "149" ltac_term:(G)) | idtac "SSR	order.1g	149	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.mul); elpi z_report "order.1g" "150" ltac_term:(G)) | idtac "SSR	order.1g	150	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.mul); elpi z_report "order.1g" "151" ltac_term:(G)) | idtac "SSR	order.1g	151	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.mul); elpi z_report "order.1g" "152" ltac_term:(G)) | idtac "SSR	order.1g	152	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (X * _)); elpi z_report "order.1g" "153" ltac_term:(G)) | idtac "SSR	order.1g	153	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (X * _) = _); elpi z_report "order.1g" "154" ltac_term:(G)) | idtac "SSR	order.1g	154	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ * (X * _) = _); elpi z_report "order.1g" "155" ltac_term:(G)) | idtac "SSR	order.1g	155	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "order.1g" "156" ltac_term:(G)) | idtac "SSR	order.1g	156	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * b); elpi z_report "order.1g" "157" ltac_term:(G)) | idtac "SSR	order.1g	157	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "order.1g" "158" ltac_term:(G)) | idtac "SSR	order.1g	158	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "order.1g" "159" ltac_term:(G)) | idtac "SSR	order.1g	159	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X * b); elpi z_report "order.1g" "160" ltac_term:(G)) | idtac "SSR	order.1g	160	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (_ * X)); elpi z_report "order.1g" "161" ltac_term:(G)) | idtac "SSR	order.1g	161	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (_ * X) = _); elpi z_report "order.1g" "162" ltac_term:(G)) | idtac "SSR	order.1g	162	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ * (_ * X) = _); elpi z_report "order.1g" "163" ltac_term:(G)) | idtac "SSR	order.1g	163	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "order.1g" "164" ltac_term:(G)) | idtac "SSR	order.1g	164	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a * X); elpi z_report "order.1g" "165" ltac_term:(G)) | idtac "SSR	order.1g	165	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(b); elpi z_report "order.1g" "166" ltac_term:(G)) | idtac "SSR	order.1g	166	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(b); elpi z_report "order.1g" "167" ltac_term:(G)) | idtac "SSR	order.1g	167	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in a * X); elpi z_report "order.1g" "168" ltac_term:(G)) | idtac "SSR	order.1g	168	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "order.1g" "169" ltac_term:(G)) | idtac "SSR	order.1g	169	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "order.1g" "170" ltac_term:(G)) | idtac "SSR	order.1g	170	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a * b * (a * b) = X); elpi z_report "order.1g" "171" ltac_term:(G)) | idtac "SSR	order.1g	171	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "order.1g" "172" ltac_term:(G)) | idtac "SSR	order.1g	172	error" ].
Abort.

Goal forall f : nat -> nat, f (f (f 0)) = f (f 1).
intros f.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _); elpi z_report "order.2" "1" ltac_term:(G)) | idtac "SSR	order.2	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f (f _)); elpi z_report "order.2" "2" ltac_term:(G)) | idtac "SSR	order.2	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 1); elpi z_report "order.2" "3" ltac_term:(G)) | idtac "SSR	order.2	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f X)); elpi z_report "order.2" "4" ltac_term:(G)) | idtac "SSR	order.2	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(f _); elpi z_report "order.2" "5" ltac_term:(G)) | idtac "SSR	order.2	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ in X in _ = X); elpi z_report "order.2" "6" ltac_term:(G)) | idtac "SSR	order.2	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 as X in f (f X)); elpi z_report "order.2" "7" ltac_term:(G)) | idtac "SSR	order.2	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "order.2g" "1" ltac_term:(G)) | idtac "SSR	order.2g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (f (f 0)) = f (f 1)); elpi z_report "order.2g" "2" ltac_term:(G)) | idtac "SSR	order.2g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "order.2g" "3" ltac_term:(G)) | idtac "SSR	order.2g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "order.2g" "4" ltac_term:(G)) | idtac "SSR	order.2g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "order.2g" "5" ltac_term:(G)) | idtac "SSR	order.2g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "order.2g" "6" ltac_term:(G)) | idtac "SSR	order.2g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _); elpi z_report "order.2g" "7" ltac_term:(G)) | idtac "SSR	order.2g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "order.2g" "8" ltac_term:(G)) | idtac "SSR	order.2g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in X = _); elpi z_report "order.2g" "9" ltac_term:(G)) | idtac "SSR	order.2g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (f (f 0))); elpi z_report "order.2g" "10" ltac_term:(G)) | idtac "SSR	order.2g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f); elpi z_report "order.2g" "11" ltac_term:(G)) | idtac "SSR	order.2g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f); elpi z_report "order.2g" "12" ltac_term:(G)) | idtac "SSR	order.2g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X); elpi z_report "order.2g" "13" ltac_term:(G)) | idtac "SSR	order.2g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in f X); elpi z_report "order.2g" "14" ltac_term:(G)) | idtac "SSR	order.2g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X = _); elpi z_report "order.2g" "15" ltac_term:(G)) | idtac "SSR	order.2g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f (f 0)); elpi z_report "order.2g" "16" ltac_term:(G)) | idtac "SSR	order.2g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in f X = _); elpi z_report "order.2g" "17" ltac_term:(G)) | idtac "SSR	order.2g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f (f 0) in X in X = _); elpi z_report "order.2g" "18" ltac_term:(G)) | idtac "SSR	order.2g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (f 0)); elpi z_report "order.2g" "19" ltac_term:(G)) | idtac "SSR	order.2g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(f); elpi z_report "order.2g" "20" ltac_term:(G)) | idtac "SSR	order.2g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(f); elpi z_report "order.2g" "21" ltac_term:(G)) | idtac "SSR	order.2g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0); elpi z_report "order.2g" "22" ltac_term:(G)) | idtac "SSR	order.2g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f X)); elpi z_report "order.2g" "23" ltac_term:(G)) | idtac "SSR	order.2g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 as X in f X); elpi z_report "order.2g" "24" ltac_term:(G)) | idtac "SSR	order.2g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 in X in f X); elpi z_report "order.2g" "25" ltac_term:(G)) | idtac "SSR	order.2g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 in X in X = _); elpi z_report "order.2g" "26" ltac_term:(G)) | idtac "SSR	order.2g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in f (f X)); elpi z_report "order.2g" "27" ltac_term:(G)) | idtac "SSR	order.2g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f X) = _); elpi z_report "order.2g" "28" ltac_term:(G)) | idtac "SSR	order.2g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 0 in X in f X = _); elpi z_report "order.2g" "29" ltac_term:(G)) | idtac "SSR	order.2g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in f (f X) = _); elpi z_report "order.2g" "30" ltac_term:(G)) | idtac "SSR	order.2g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f 0); elpi z_report "order.2g" "31" ltac_term:(G)) | idtac "SSR	order.2g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(f); elpi z_report "order.2g" "32" ltac_term:(G)) | idtac "SSR	order.2g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(f); elpi z_report "order.2g" "33" ltac_term:(G)) | idtac "SSR	order.2g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f (f X))); elpi z_report "order.2g" "34" ltac_term:(G)) | idtac "SSR	order.2g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f (f X)) = _); elpi z_report "order.2g" "35" ltac_term:(G)) | idtac "SSR	order.2g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "order.2g" "36" ltac_term:(G)) | idtac "SSR	order.2g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "order.2g" "37" ltac_term:(G)) | idtac "SSR	order.2g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "order.2g" "38" ltac_term:(G)) | idtac "SSR	order.2g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ = X); elpi z_report "order.2g" "39" ltac_term:(G)) | idtac "SSR	order.2g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f (f 1)); elpi z_report "order.2g" "40" ltac_term:(G)) | idtac "SSR	order.2g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (f 1)); elpi z_report "order.2g" "41" ltac_term:(G)) | idtac "SSR	order.2g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(f); elpi z_report "order.2g" "42" ltac_term:(G)) | idtac "SSR	order.2g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(f); elpi z_report "order.2g" "43" ltac_term:(G)) | idtac "SSR	order.2g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 1); elpi z_report "order.2g" "44" ltac_term:(G)) | idtac "SSR	order.2g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f X); elpi z_report "order.2g" "45" ltac_term:(G)) | idtac "SSR	order.2g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 1 as X in f X); elpi z_report "order.2g" "46" ltac_term:(G)) | idtac "SSR	order.2g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f 1 in X in _ = X); elpi z_report "order.2g" "47" ltac_term:(G)) | idtac "SSR	order.2g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ = f X); elpi z_report "order.2g" "48" ltac_term:(G)) | idtac "SSR	order.2g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f 1); elpi z_report "order.2g" "49" ltac_term:(G)) | idtac "SSR	order.2g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f); elpi z_report "order.2g" "50" ltac_term:(G)) | idtac "SSR	order.2g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(f); elpi z_report "order.2g" "51" ltac_term:(G)) | idtac "SSR	order.2g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(f); elpi z_report "order.2g" "52" ltac_term:(G)) | idtac "SSR	order.2g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "order.2g" "53" ltac_term:(G)) | idtac "SSR	order.2g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f X); elpi z_report "order.2g" "54" ltac_term:(G)) | idtac "SSR	order.2g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X); elpi z_report "order.2g" "55" ltac_term:(G)) | idtac "SSR	order.2g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in f (f X)); elpi z_report "order.2g" "56" ltac_term:(G)) | idtac "SSR	order.2g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = f X); elpi z_report "order.2g" "57" ltac_term:(G)) | idtac "SSR	order.2g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (f X)); elpi z_report "order.2g" "58" ltac_term:(G)) | idtac "SSR	order.2g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = f (f X)); elpi z_report "order.2g" "59" ltac_term:(G)) | idtac "SSR	order.2g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "order.2g" "60" ltac_term:(G)) | idtac "SSR	order.2g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "order.2g" "61" ltac_term:(G)) | idtac "SSR	order.2g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "order.2g" "62" ltac_term:(G)) | idtac "SSR	order.2g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "order.2g" "63" ltac_term:(G)) | idtac "SSR	order.2g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (S X)); elpi z_report "order.2g" "64" ltac_term:(G)) | idtac "SSR	order.2g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (f (S X))); elpi z_report "order.2g" "65" ltac_term:(G)) | idtac "SSR	order.2g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (f (S X))); elpi z_report "order.2g" "66" ltac_term:(G)) | idtac "SSR	order.2g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "order.2g" "67" ltac_term:(G)) | idtac "SSR	order.2g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "order.2g" "68" ltac_term:(G)) | idtac "SSR	order.2g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "order.2g" "69" ltac_term:(G)) | idtac "SSR	order.2g	69	error" ].
Abort.

(* occurrences: equal copies, copies equal up to conversion (compared
   argument by argument), numerals *)
Goal forall m : nat, 2 + m = (1 + 1) + m /\ S (S m) = 2 + m /\ 2 = 1 + 1.
intros m.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 + m); elpi z_report "occ.1" "1" ltac_term:(G)) | idtac "SSR	occ.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m); elpi z_report "occ.1" "2" ltac_term:(G)) | idtac "SSR	occ.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + 1); elpi z_report "occ.1" "3" ltac_term:(G)) | idtac "SSR	occ.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2); elpi z_report "occ.1" "4" ltac_term:(G)) | idtac "SSR	occ.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "occ.1" "5" ltac_term:(G)) | idtac "SSR	occ.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 + _); elpi z_report "occ.1" "6" ltac_term:(G)) | idtac "SSR	occ.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(2 + m); elpi z_report "occ.1" "7" ltac_term:(G)) | idtac "SSR	occ.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + m); elpi z_report "occ.1" "8" ltac_term:(G)) | idtac "SSR	occ.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ X); elpi z_report "occ.1" "9" ltac_term:(G)) | idtac "SSR	occ.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "occ.1g" "1" ltac_term:(G)) | idtac "SSR	occ.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 + m = 1 + 1 + m /\ S (S m) = 2 + m /\ 2 = 1 + 1); elpi z_report "occ.1g" "2" ltac_term:(G)) | idtac "SSR	occ.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "occ.1g" "3" ltac_term:(G)) | idtac "SSR	occ.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "occ.1g" "4" ltac_term:(G)) | idtac "SSR	occ.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "occ.1g" "5" ltac_term:(G)) | idtac "SSR	occ.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "occ.1g" "6" ltac_term:(G)) | idtac "SSR	occ.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "occ.1g" "7" ltac_term:(G)) | idtac "SSR	occ.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ = _); elpi z_report "occ.1g" "8" ltac_term:(G)) | idtac "SSR	occ.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 + m = 1 + 1 + m); elpi z_report "occ.1g" "9" ltac_term:(G)) | idtac "SSR	occ.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "occ.1g" "10" ltac_term:(G)) | idtac "SSR	occ.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "occ.1g" "11" ltac_term:(G)) | idtac "SSR	occ.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "occ.1g" "12" ltac_term:(G)) | idtac "SSR	occ.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "occ.1g" "13" ltac_term:(G)) | idtac "SSR	occ.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "occ.1g" "14" ltac_term:(G)) | idtac "SSR	occ.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _ /\ _); elpi z_report "occ.1g" "15" ltac_term:(G)) | idtac "SSR	occ.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "occ.1g" "16" ltac_term:(G)) | idtac "SSR	occ.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "occ.1g" "17" ltac_term:(G)) | idtac "SSR	occ.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "occ.1g" "18" ltac_term:(G)) | idtac "SSR	occ.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ _); elpi z_report "occ.1g" "19" ltac_term:(G)) | idtac "SSR	occ.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _); elpi z_report "occ.1g" "20" ltac_term:(G)) | idtac "SSR	occ.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X = _); elpi z_report "occ.1g" "21" ltac_term:(G)) | idtac "SSR	occ.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _ as X in X = _); elpi z_report "occ.1g" "22" ltac_term:(G)) | idtac "SSR	occ.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _ in X in X /\ _); elpi z_report "occ.1g" "23" ltac_term:(G)) | idtac "SSR	occ.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 + m); elpi z_report "occ.1g" "24" ltac_term:(G)) | idtac "SSR	occ.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "occ.1g" "25" ltac_term:(G)) | idtac "SSR	occ.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "occ.1g" "26" ltac_term:(G)) | idtac "SSR	occ.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X /\ _); elpi z_report "occ.1g" "27" ltac_term:(G)) | idtac "SSR	occ.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _ /\ _); elpi z_report "occ.1g" "28" ltac_term:(G)) | idtac "SSR	occ.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _ /\ _); elpi z_report "occ.1g" "29" ltac_term:(G)) | idtac "SSR	occ.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ = _ /\ _); elpi z_report "occ.1g" "30" ltac_term:(G)) | idtac "SSR	occ.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "occ.1g" "31" ltac_term:(G)) | idtac "SSR	occ.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "occ.1g" "32" ltac_term:(G)) | idtac "SSR	occ.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _); elpi z_report "occ.1g" "33" ltac_term:(G)) | idtac "SSR	occ.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "occ.1g" "34" ltac_term:(G)) | idtac "SSR	occ.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "occ.1g" "35" ltac_term:(G)) | idtac "SSR	occ.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ = _); elpi z_report "occ.1g" "36" ltac_term:(G)) | idtac "SSR	occ.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2); elpi z_report "occ.1g" "37" ltac_term:(G)) | idtac "SSR	occ.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "occ.1g" "38" ltac_term:(G)) | idtac "SSR	occ.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + _); elpi z_report "occ.1g" "39" ltac_term:(G)) | idtac "SSR	occ.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in X + _); elpi z_report "occ.1g" "40" ltac_term:(G)) | idtac "SSR	occ.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X = _); elpi z_report "occ.1g" "41" ltac_term:(G)) | idtac "SSR	occ.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + _ = _); elpi z_report "occ.1g" "42" ltac_term:(G)) | idtac "SSR	occ.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in X + _ = _); elpi z_report "occ.1g" "43" ltac_term:(G)) | idtac "SSR	occ.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "occ.1g" "44" ltac_term:(G)) | idtac "SSR	occ.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "occ.1g" "45" ltac_term:(G)) | idtac "SSR	occ.1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = _ /\ _); elpi z_report "occ.1g" "46" ltac_term:(G)) | idtac "SSR	occ.1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ = _ /\ _); elpi z_report "occ.1g" "47" ltac_term:(G)) | idtac "SSR	occ.1g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X + _ = _ /\ _); elpi z_report "occ.1g" "48" ltac_term:(G)) | idtac "SSR	occ.1g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "occ.1g" "49" ltac_term:(G)) | idtac "SSR	occ.1g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "occ.1g" "50" ltac_term:(G)) | idtac "SSR	occ.1g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = _); elpi z_report "occ.1g" "51" ltac_term:(G)) | idtac "SSR	occ.1g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X + _); elpi z_report "occ.1g" "52" ltac_term:(G)) | idtac "SSR	occ.1g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _); elpi z_report "occ.1g" "53" ltac_term:(G)) | idtac "SSR	occ.1g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X + _ = _); elpi z_report "occ.1g" "54" ltac_term:(G)) | idtac "SSR	occ.1g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ = _); elpi z_report "occ.1g" "55" ltac_term:(G)) | idtac "SSR	occ.1g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X + _ = _); elpi z_report "occ.1g" "56" ltac_term:(G)) | idtac "SSR	occ.1g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "occ.1g" "57" ltac_term:(G)) | idtac "SSR	occ.1g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "occ.1g" "58" ltac_term:(G)) | idtac "SSR	occ.1g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "occ.1g" "59" ltac_term:(G)) | idtac "SSR	occ.1g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in S X); elpi z_report "occ.1g" "60" ltac_term:(G)) | idtac "SSR	occ.1g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X = _); elpi z_report "occ.1g" "61" ltac_term:(G)) | idtac "SSR	occ.1g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X + _); elpi z_report "occ.1g" "62" ltac_term:(G)) | idtac "SSR	occ.1g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X /\ _); elpi z_report "occ.1g" "63" ltac_term:(G)) | idtac "SSR	occ.1g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X + _); elpi z_report "occ.1g" "64" ltac_term:(G)) | idtac "SSR	occ.1g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in S X + _); elpi z_report "occ.1g" "65" ltac_term:(G)) | idtac "SSR	occ.1g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in X + _ = _); elpi z_report "occ.1g" "66" ltac_term:(G)) | idtac "SSR	occ.1g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X + _ = _); elpi z_report "occ.1g" "67" ltac_term:(G)) | idtac "SSR	occ.1g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in S X + _ = _); elpi z_report "occ.1g" "68" ltac_term:(G)) | idtac "SSR	occ.1g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "occ.1g" "69" ltac_term:(G)) | idtac "SSR	occ.1g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "occ.1g" "70" ltac_term:(G)) | idtac "SSR	occ.1g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) + _ = _ /\ _); elpi z_report "occ.1g" "71" ltac_term:(G)) | idtac "SSR	occ.1g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "occ.1g" "72" ltac_term:(G)) | idtac "SSR	occ.1g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) + _ = _); elpi z_report "occ.1g" "73" ltac_term:(G)) | idtac "SSR	occ.1g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "occ.1g" "74" ltac_term:(G)) | idtac "SSR	occ.1g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "occ.1g" "75" ltac_term:(G)) | idtac "SSR	occ.1g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X)); elpi z_report "occ.1g" "76" ltac_term:(G)) | idtac "SSR	occ.1g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X) + _); elpi z_report "occ.1g" "77" ltac_term:(G)) | idtac "SSR	occ.1g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S (S X) + _ = _); elpi z_report "occ.1g" "78" ltac_term:(G)) | idtac "SSR	occ.1g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _ /\ _); elpi z_report "occ.1g" "79" ltac_term:(G)) | idtac "SSR	occ.1g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "occ.1g" "80" ltac_term:(G)) | idtac "SSR	occ.1g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "occ.1g" "81" ltac_term:(G)) | idtac "SSR	occ.1g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "occ.1g" "82" ltac_term:(G)) | idtac "SSR	occ.1g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "occ.1g" "83" ltac_term:(G)) | idtac "SSR	occ.1g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ + X); elpi z_report "occ.1g" "84" ltac_term:(G)) | idtac "SSR	occ.1g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ + X = _); elpi z_report "occ.1g" "85" ltac_term:(G)) | idtac "SSR	occ.1g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "occ.1g" "86" ltac_term:(G)) | idtac "SSR	occ.1g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X /\ _); elpi z_report "occ.1g" "87" ltac_term:(G)) | idtac "SSR	occ.1g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "occ.1g" "88" ltac_term:(G)) | idtac "SSR	occ.1g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "occ.1g" "89" ltac_term:(G)) | idtac "SSR	occ.1g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + 1 + _); elpi z_report "occ.1g" "90" ltac_term:(G)) | idtac "SSR	occ.1g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + 1 + _ in X in X /\ _); elpi z_report "occ.1g" "91" ltac_term:(G)) | idtac "SSR	occ.1g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = X); elpi z_report "occ.1g" "92" ltac_term:(G)) | idtac "SSR	occ.1g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _ as X in _ = X); elpi z_report "occ.1g" "93" ltac_term:(G)) | idtac "SSR	occ.1g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 + 1 + _); elpi z_report "occ.1g" "94" ltac_term:(G)) | idtac "SSR	occ.1g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 + 1 + m); elpi z_report "occ.1g" "95" ltac_term:(G)) | idtac "SSR	occ.1g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 + 1 + _ in X in X /\ _); elpi z_report "occ.1g" "96" ltac_term:(G)) | idtac "SSR	occ.1g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "occ.1g" "97" ltac_term:(G)) | idtac "SSR	occ.1g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "occ.1g" "98" ltac_term:(G)) | idtac "SSR	occ.1g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _ in X in X /\ _); elpi z_report "occ.1g" "99" ltac_term:(G)) | idtac "SSR	occ.1g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ /\ _); elpi z_report "occ.1g" "100" ltac_term:(G)) | idtac "SSR	occ.1g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _ in X in _ = X /\ _); elpi z_report "occ.1g" "101" ltac_term:(G)) | idtac "SSR	occ.1g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X + _ /\ _); elpi z_report "occ.1g" "102" ltac_term:(G)) | idtac "SSR	occ.1g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "occ.1g" "103" ltac_term:(G)) | idtac "SSR	occ.1g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "occ.1g" "104" ltac_term:(G)) | idtac "SSR	occ.1g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _ in X in _ = X); elpi z_report "occ.1g" "105" ltac_term:(G)) | idtac "SSR	occ.1g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X + _); elpi z_report "occ.1g" "106" ltac_term:(G)) | idtac "SSR	occ.1g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + _); elpi z_report "occ.1g" "107" ltac_term:(G)) | idtac "SSR	occ.1g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + _ as X in X + _); elpi z_report "occ.1g" "108" ltac_term:(G)) | idtac "SSR	occ.1g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = X + _); elpi z_report "occ.1g" "109" ltac_term:(G)) | idtac "SSR	occ.1g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + 1); elpi z_report "occ.1g" "110" ltac_term:(G)) | idtac "SSR	occ.1g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + _ in X in _ = X); elpi z_report "occ.1g" "111" ltac_term:(G)) | idtac "SSR	occ.1g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _ as X in _ = X + _); elpi z_report "occ.1g" "112" ltac_term:(G)) | idtac "SSR	occ.1g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "occ.1g" "113" ltac_term:(G)) | idtac "SSR	occ.1g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "occ.1g" "114" ltac_term:(G)) | idtac "SSR	occ.1g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ + _ /\ _); elpi z_report "occ.1g" "115" ltac_term:(G)) | idtac "SSR	occ.1g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X + _ + _ /\ _); elpi z_report "occ.1g" "116" ltac_term:(G)) | idtac "SSR	occ.1g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "occ.1g" "117" ltac_term:(G)) | idtac "SSR	occ.1g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ + _); elpi z_report "occ.1g" "118" ltac_term:(G)) | idtac "SSR	occ.1g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ + _); elpi z_report "occ.1g" "119" ltac_term:(G)) | idtac "SSR	occ.1g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X + _ + _); elpi z_report "occ.1g" "120" ltac_term:(G)) | idtac "SSR	occ.1g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "occ.1g" "121" ltac_term:(G)) | idtac "SSR	occ.1g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "occ.1g" "122" ltac_term:(G)) | idtac "SSR	occ.1g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + 1); elpi z_report "occ.1g" "123" ltac_term:(G)) | idtac "SSR	occ.1g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 as X in X + _); elpi z_report "occ.1g" "124" ltac_term:(G)) | idtac "SSR	occ.1g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in X /\ _); elpi z_report "occ.1g" "125" ltac_term:(G)) | idtac "SSR	occ.1g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in _ = X); elpi z_report "occ.1g" "126" ltac_term:(G)) | idtac "SSR	occ.1g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X + _ + _); elpi z_report "occ.1g" "127" ltac_term:(G)) | idtac "SSR	occ.1g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in X + _ + _); elpi z_report "occ.1g" "128" ltac_term:(G)) | idtac "SSR	occ.1g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in _ = X + _); elpi z_report "occ.1g" "129" ltac_term:(G)) | idtac "SSR	occ.1g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in _ = X /\ _); elpi z_report "occ.1g" "130" ltac_term:(G)) | idtac "SSR	occ.1g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = X + _ + _); elpi z_report "occ.1g" "131" ltac_term:(G)) | idtac "SSR	occ.1g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in _ = X + _ + _); elpi z_report "occ.1g" "132" ltac_term:(G)) | idtac "SSR	occ.1g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "occ.1g" "133" ltac_term:(G)) | idtac "SSR	occ.1g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "occ.1g" "134" ltac_term:(G)) | idtac "SSR	occ.1g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X + _ + _ /\ _); elpi z_report "occ.1g" "135" ltac_term:(G)) | idtac "SSR	occ.1g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ + _); elpi z_report "occ.1g" "136" ltac_term:(G)) | idtac "SSR	occ.1g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X + _ + _); elpi z_report "occ.1g" "137" ltac_term:(G)) | idtac "SSR	occ.1g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "occ.1g" "138" ltac_term:(G)) | idtac "SSR	occ.1g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "occ.1g" "139" ltac_term:(G)) | idtac "SSR	occ.1g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X + 1); elpi z_report "occ.1g" "140" ltac_term:(G)) | idtac "SSR	occ.1g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X + _ + _); elpi z_report "occ.1g" "141" ltac_term:(G)) | idtac "SSR	occ.1g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = S X + _ + _); elpi z_report "occ.1g" "142" ltac_term:(G)) | idtac "SSR	occ.1g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X + _ /\ _); elpi z_report "occ.1g" "143" ltac_term:(G)) | idtac "SSR	occ.1g	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = _ + X + _ /\ _); elpi z_report "occ.1g" "144" ltac_term:(G)) | idtac "SSR	occ.1g	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X /\ _); elpi z_report "occ.1g" "145" ltac_term:(G)) | idtac "SSR	occ.1g	145	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X); elpi z_report "occ.1g" "146" ltac_term:(G)) | idtac "SSR	occ.1g	146	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "occ.1g" "147" ltac_term:(G)) | idtac "SSR	occ.1g	147	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X + _); elpi z_report "occ.1g" "148" ltac_term:(G)) | idtac "SSR	occ.1g	148	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X + _); elpi z_report "occ.1g" "149" ltac_term:(G)) | idtac "SSR	occ.1g	149	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X /\ _); elpi z_report "occ.1g" "150" ltac_term:(G)) | idtac "SSR	occ.1g	150	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X + _); elpi z_report "occ.1g" "151" ltac_term:(G)) | idtac "SSR	occ.1g	151	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = _ + X + _); elpi z_report "occ.1g" "152" ltac_term:(G)) | idtac "SSR	occ.1g	152	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "occ.1g" "153" ltac_term:(G)) | idtac "SSR	occ.1g	153	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "occ.1g" "154" ltac_term:(G)) | idtac "SSR	occ.1g	154	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in 1 + X); elpi z_report "occ.1g" "155" ltac_term:(G)) | idtac "SSR	occ.1g	155	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in X /\ _); elpi z_report "occ.1g" "156" ltac_term:(G)) | idtac "SSR	occ.1g	156	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in _ + X); elpi z_report "occ.1g" "157" ltac_term:(G)) | idtac "SSR	occ.1g	157	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in _ = X); elpi z_report "occ.1g" "158" ltac_term:(G)) | idtac "SSR	occ.1g	158	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ + X + _); elpi z_report "occ.1g" "159" ltac_term:(G)) | idtac "SSR	occ.1g	159	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in _ + X + _); elpi z_report "occ.1g" "160" ltac_term:(G)) | idtac "SSR	occ.1g	160	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in _ = X + _); elpi z_report "occ.1g" "161" ltac_term:(G)) | idtac "SSR	occ.1g	161	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in _ = X /\ _); elpi z_report "occ.1g" "162" ltac_term:(G)) | idtac "SSR	occ.1g	162	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = _ + X + _); elpi z_report "occ.1g" "163" ltac_term:(G)) | idtac "SSR	occ.1g	163	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in _ = _ + X + _); elpi z_report "occ.1g" "164" ltac_term:(G)) | idtac "SSR	occ.1g	164	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(S); elpi z_report "occ.1g" "165" ltac_term:(G)) | idtac "SSR	occ.1g	165	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(S); elpi z_report "occ.1g" "166" ltac_term:(G)) | idtac "SSR	occ.1g	166	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + S X + _ /\ _); elpi z_report "occ.1g" "167" ltac_term:(G)) | idtac "SSR	occ.1g	167	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X + _); elpi z_report "occ.1g" "168" ltac_term:(G)) | idtac "SSR	occ.1g	168	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + S X + _); elpi z_report "occ.1g" "169" ltac_term:(G)) | idtac "SSR	occ.1g	169	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "occ.1g" "170" ltac_term:(G)) | idtac "SSR	occ.1g	170	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "occ.1g" "171" ltac_term:(G)) | idtac "SSR	occ.1g	171	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ + S X); elpi z_report "occ.1g" "172" ltac_term:(G)) | idtac "SSR	occ.1g	172	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ + S X + _); elpi z_report "occ.1g" "173" ltac_term:(G)) | idtac "SSR	occ.1g	173	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = _ + S X + _); elpi z_report "occ.1g" "174" ltac_term:(G)) | idtac "SSR	occ.1g	174	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X /\ _); elpi z_report "occ.1g" "175" ltac_term:(G)) | idtac "SSR	occ.1g	175	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "occ.1g" "176" ltac_term:(G)) | idtac "SSR	occ.1g	176	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + 1 + X); elpi z_report "occ.1g" "177" ltac_term:(G)) | idtac "SSR	occ.1g	177	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "occ.1g" "178" ltac_term:(G)) | idtac "SSR	occ.1g	178	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "occ.1g" "179" ltac_term:(G)) | idtac "SSR	occ.1g	179	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ = _ + X); elpi z_report "occ.1g" "180" ltac_term:(G)) | idtac "SSR	occ.1g	180	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in 1 + 1 + X); elpi z_report "occ.1g" "181" ltac_term:(G)) | idtac "SSR	occ.1g	181	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "occ.1g" "182" ltac_term:(G)) | idtac "SSR	occ.1g	182	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _ as X in _ /\ X); elpi z_report "occ.1g" "183" ltac_term:(G)) | idtac "SSR	occ.1g	183	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S (S m) = _ /\ _); elpi z_report "occ.1g" "184" ltac_term:(G)) | idtac "SSR	occ.1g	184	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S (S m) = 2 + m /\ 2 = 1 + 1); elpi z_report "occ.1g" "185" ltac_term:(G)) | idtac "SSR	occ.1g	185	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "occ.1g" "186" ltac_term:(G)) | idtac "SSR	occ.1g	186	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(and); elpi z_report "occ.1g" "187" ltac_term:(G)) | idtac "SSR	occ.1g	187	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(and); elpi z_report "occ.1g" "188" ltac_term:(G)) | idtac "SSR	occ.1g	188	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ in X in _ /\ X); elpi z_report "occ.1g" "189" ltac_term:(G)) | idtac "SSR	occ.1g	189	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X /\ _); elpi z_report "occ.1g" "190" ltac_term:(G)) | idtac "SSR	occ.1g	190	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X /\ _); elpi z_report "occ.1g" "191" ltac_term:(G)) | idtac "SSR	occ.1g	191	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S (S m) = _ as X in X /\ _); elpi z_report "occ.1g" "192" ltac_term:(G)) | idtac "SSR	occ.1g	192	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ 2 = 1 + 1); elpi z_report "occ.1g" "193" ltac_term:(G)) | idtac "SSR	occ.1g	193	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S (S m) = _); elpi z_report "occ.1g" "194" ltac_term:(G)) | idtac "SSR	occ.1g	194	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S (S m) = _); elpi z_report "occ.1g" "195" ltac_term:(G)) | idtac "SSR	occ.1g	195	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S (S m) = 2 + m); elpi z_report "occ.1g" "196" ltac_term:(G)) | idtac "SSR	occ.1g	196	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "occ.1g" "197" ltac_term:(G)) | idtac "SSR	occ.1g	197	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "occ.1g" "198" ltac_term:(G)) | idtac "SSR	occ.1g	198	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "occ.1g" "199" ltac_term:(G)) | idtac "SSR	occ.1g	199	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "occ.1g" "200" ltac_term:(G)) | idtac "SSR	occ.1g	200	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ /\ X); elpi z_report "occ.1g" "201" ltac_term:(G)) | idtac "SSR	occ.1g	201	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S (S m)); elpi z_report "occ.1g" "202" ltac_term:(G)) | idtac "SSR	occ.1g	202	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X = _ /\ _); elpi z_report "occ.1g" "203" ltac_term:(G)) | idtac "SSR	occ.1g	203	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ /\ X /\ _); elpi z_report "occ.1g" "204" ltac_term:(G)) | idtac "SSR	occ.1g	204	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _ /\ _); elpi z_report "occ.1g" "205" ltac_term:(G)) | idtac "SSR	occ.1g	205	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = 2 + _ /\ _); elpi z_report "occ.1g" "206" ltac_term:(G)) | idtac "SSR	occ.1g	206	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ X = _ /\ _); elpi z_report "occ.1g" "207" ltac_term:(G)) | idtac "SSR	occ.1g	207	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X /\ 2 = 1 + 1); elpi z_report "occ.1g" "208" ltac_term:(G)) | idtac "SSR	occ.1g	208	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X = _); elpi z_report "occ.1g" "209" ltac_term:(G)) | idtac "SSR	occ.1g	209	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = 2 + _); elpi z_report "occ.1g" "210" ltac_term:(G)) | idtac "SSR	occ.1g	210	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in X = _); elpi z_report "occ.1g" "211" ltac_term:(G)) | idtac "SSR	occ.1g	211	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S (S m)); elpi z_report "occ.1g" "212" ltac_term:(G)) | idtac "SSR	occ.1g	212	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X = 2 + _); elpi z_report "occ.1g" "213" ltac_term:(G)) | idtac "SSR	occ.1g	213	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(S); elpi z_report "occ.1g" "214" ltac_term:(G)) | idtac "SSR	occ.1g	214	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(S); elpi z_report "occ.1g" "215" ltac_term:(G)) | idtac "SSR	occ.1g	215	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S m); elpi z_report "occ.1g" "216" ltac_term:(G)) | idtac "SSR	occ.1g	216	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S m as X in S X); elpi z_report "occ.1g" "217" ltac_term:(G)) | idtac "SSR	occ.1g	217	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S m in X in _ /\ X); elpi z_report "occ.1g" "218" ltac_term:(G)) | idtac "SSR	occ.1g	218	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X = _ /\ _); elpi z_report "occ.1g" "219" ltac_term:(G)) | idtac "SSR	occ.1g	219	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S m in X in _ /\ X /\ _); elpi z_report "occ.1g" "220" ltac_term:(G)) | idtac "SSR	occ.1g	220	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X = _ /\ _); elpi z_report "occ.1g" "221" ltac_term:(G)) | idtac "SSR	occ.1g	221	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ S X = _ /\ _); elpi z_report "occ.1g" "222" ltac_term:(G)) | idtac "SSR	occ.1g	222	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ S X = _ /\ _); elpi z_report "occ.1g" "223" ltac_term:(G)) | idtac "SSR	occ.1g	223	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S m in X in X = 2 + _ /\ _); elpi z_report "occ.1g" "224" ltac_term:(G)) | idtac "SSR	occ.1g	224	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S m in X in X /\ 2 = 1 + 1); elpi z_report "occ.1g" "225" ltac_term:(G)) | idtac "SSR	occ.1g	225	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X = _); elpi z_report "occ.1g" "226" ltac_term:(G)) | idtac "SSR	occ.1g	226	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X = _); elpi z_report "occ.1g" "227" ltac_term:(G)) | idtac "SSR	occ.1g	227	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S m in X in X = 2 + _); elpi z_report "occ.1g" "228" ltac_term:(G)) | idtac "SSR	occ.1g	228	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S m); elpi z_report "occ.1g" "229" ltac_term:(G)) | idtac "SSR	occ.1g	229	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X = _); elpi z_report "occ.1g" "230" ltac_term:(G)) | idtac "SSR	occ.1g	230	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in S X = _); elpi z_report "occ.1g" "231" ltac_term:(G)) | idtac "SSR	occ.1g	231	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S m in X in X = 2 + _); elpi z_report "occ.1g" "232" ltac_term:(G)) | idtac "SSR	occ.1g	232	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(S); elpi z_report "occ.1g" "233" ltac_term:(G)) | idtac "SSR	occ.1g	233	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(S); elpi z_report "occ.1g" "234" ltac_term:(G)) | idtac "SSR	occ.1g	234	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) = _ /\ _); elpi z_report "occ.1g" "235" ltac_term:(G)) | idtac "SSR	occ.1g	235	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ S (S X) = _ /\ _); elpi z_report "occ.1g" "236" ltac_term:(G)) | idtac "SSR	occ.1g	236	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) = _); elpi z_report "occ.1g" "237" ltac_term:(G)) | idtac "SSR	occ.1g	237	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "occ.1g" "238" ltac_term:(G)) | idtac "SSR	occ.1g	238	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "occ.1g" "239" ltac_term:(G)) | idtac "SSR	occ.1g	239	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S (S X) = _); elpi z_report "occ.1g" "240" ltac_term:(G)) | idtac "SSR	occ.1g	240	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ X); elpi z_report "occ.1g" "241" ltac_term:(G)) | idtac "SSR	occ.1g	241	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ X /\ _); elpi z_report "occ.1g" "242" ltac_term:(G)) | idtac "SSR	occ.1g	242	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X /\ _); elpi z_report "occ.1g" "243" ltac_term:(G)) | idtac "SSR	occ.1g	243	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ /\ _ = X /\ _); elpi z_report "occ.1g" "244" ltac_term:(G)) | idtac "SSR	occ.1g	244	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S m) = X /\ _); elpi z_report "occ.1g" "245" ltac_term:(G)) | idtac "SSR	occ.1g	245	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in S (S m) = X /\ _); elpi z_report "occ.1g" "246" ltac_term:(G)) | idtac "SSR	occ.1g	246	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ 2 = 1 + 1); elpi z_report "occ.1g" "247" ltac_term:(G)) | idtac "SSR	occ.1g	247	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 + _); elpi z_report "occ.1g" "248" ltac_term:(G)) | idtac "SSR	occ.1g	248	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S m) = X); elpi z_report "occ.1g" "249" ltac_term:(G)) | idtac "SSR	occ.1g	249	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in S (S m) = X); elpi z_report "occ.1g" "250" ltac_term:(G)) | idtac "SSR	occ.1g	250	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(2 + _); elpi z_report "occ.1g" "251" ltac_term:(G)) | idtac "SSR	occ.1g	251	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(2 + m); elpi z_report "occ.1g" "252" ltac_term:(G)) | idtac "SSR	occ.1g	252	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S (S m) = X); elpi z_report "occ.1g" "253" ltac_term:(G)) | idtac "SSR	occ.1g	253	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + _ as X in S (S m) = X); elpi z_report "occ.1g" "254" ltac_term:(G)) | idtac "SSR	occ.1g	254	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "occ.1g" "255" ltac_term:(G)) | idtac "SSR	occ.1g	255	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "occ.1g" "256" ltac_term:(G)) | idtac "SSR	occ.1g	256	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 in X in _ /\ X /\ _); elpi z_report "occ.1g" "257" ltac_term:(G)) | idtac "SSR	occ.1g	257	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X + _ /\ _); elpi z_report "occ.1g" "258" ltac_term:(G)) | idtac "SSR	occ.1g	258	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X + _ /\ _); elpi z_report "occ.1g" "259" ltac_term:(G)) | idtac "SSR	occ.1g	259	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ = X + _ /\ _); elpi z_report "occ.1g" "260" ltac_term:(G)) | idtac "SSR	occ.1g	260	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S (S m) = X /\ _); elpi z_report "occ.1g" "261" ltac_term:(G)) | idtac "SSR	occ.1g	261	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S m) = X + _ /\ _); elpi z_report "occ.1g" "262" ltac_term:(G)) | idtac "SSR	occ.1g	262	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 in X in X /\ 2 = 1 + 1); elpi z_report "occ.1g" "263" ltac_term:(G)) | idtac "SSR	occ.1g	263	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + m); elpi z_report "occ.1g" "264" ltac_term:(G)) | idtac "SSR	occ.1g	264	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X + _); elpi z_report "occ.1g" "265" ltac_term:(G)) | idtac "SSR	occ.1g	265	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S (S m) = X); elpi z_report "occ.1g" "266" ltac_term:(G)) | idtac "SSR	occ.1g	266	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S m) = X + _); elpi z_report "occ.1g" "267" ltac_term:(G)) | idtac "SSR	occ.1g	267	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(2); elpi z_report "occ.1g" "268" ltac_term:(G)) | idtac "SSR	occ.1g	268	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(2); elpi z_report "occ.1g" "269" ltac_term:(G)) | idtac "SSR	occ.1g	269	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 in X in _ /\ X); elpi z_report "occ.1g" "270" ltac_term:(G)) | idtac "SSR	occ.1g	270	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in X + m); elpi z_report "occ.1g" "271" ltac_term:(G)) | idtac "SSR	occ.1g	271	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in _ = X + _); elpi z_report "occ.1g" "272" ltac_term:(G)) | idtac "SSR	occ.1g	272	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in S (S m) = X); elpi z_report "occ.1g" "273" ltac_term:(G)) | idtac "SSR	occ.1g	273	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S (S m) = X + _); elpi z_report "occ.1g" "274" ltac_term:(G)) | idtac "SSR	occ.1g	274	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(S); elpi z_report "occ.1g" "275" ltac_term:(G)) | idtac "SSR	occ.1g	275	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(S); elpi z_report "occ.1g" "276" ltac_term:(G)) | idtac "SSR	occ.1g	276	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ /\ X /\ _); elpi z_report "occ.1g" "277" ltac_term:(G)) | idtac "SSR	occ.1g	277	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X + _ /\ _); elpi z_report "occ.1g" "278" ltac_term:(G)) | idtac "SSR	occ.1g	278	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = S X + _ /\ _); elpi z_report "occ.1g" "279" ltac_term:(G)) | idtac "SSR	occ.1g	279	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = S X + _ /\ _); elpi z_report "occ.1g" "280" ltac_term:(G)) | idtac "SSR	occ.1g	280	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S (S m) = X /\ _); elpi z_report "occ.1g" "281" ltac_term:(G)) | idtac "SSR	occ.1g	281	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ = S X + _ /\ _); elpi z_report "occ.1g" "282" ltac_term:(G)) | idtac "SSR	occ.1g	282	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X /\ 2 = 1 + 1); elpi z_report "occ.1g" "283" ltac_term:(G)) | idtac "SSR	occ.1g	283	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + m); elpi z_report "occ.1g" "284" ltac_term:(G)) | idtac "SSR	occ.1g	284	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X + _); elpi z_report "occ.1g" "285" ltac_term:(G)) | idtac "SSR	occ.1g	285	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X + _); elpi z_report "occ.1g" "286" ltac_term:(G)) | idtac "SSR	occ.1g	286	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = S X + _); elpi z_report "occ.1g" "287" ltac_term:(G)) | idtac "SSR	occ.1g	287	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S (S m) = X); elpi z_report "occ.1g" "288" ltac_term:(G)) | idtac "SSR	occ.1g	288	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S (S m) = X + _); elpi z_report "occ.1g" "289" ltac_term:(G)) | idtac "SSR	occ.1g	289	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(1); elpi z_report "occ.1g" "290" ltac_term:(G)) | idtac "SSR	occ.1g	290	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(1); elpi z_report "occ.1g" "291" ltac_term:(G)) | idtac "SSR	occ.1g	291	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in S X); elpi z_report "occ.1g" "292" ltac_term:(G)) | idtac "SSR	occ.1g	292	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S X + m); elpi z_report "occ.1g" "293" ltac_term:(G)) | idtac "SSR	occ.1g	293	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in S X + _); elpi z_report "occ.1g" "294" ltac_term:(G)) | idtac "SSR	occ.1g	294	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ = S X + _); elpi z_report "occ.1g" "295" ltac_term:(G)) | idtac "SSR	occ.1g	295	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in _ = S X + _); elpi z_report "occ.1g" "296" ltac_term:(G)) | idtac "SSR	occ.1g	296	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in S (S m) = X); elpi z_report "occ.1g" "297" ltac_term:(G)) | idtac "SSR	occ.1g	297	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in S (S m) = X + _); elpi z_report "occ.1g" "298" ltac_term:(G)) | idtac "SSR	occ.1g	298	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(S); elpi z_report "occ.1g" "299" ltac_term:(G)) | idtac "SSR	occ.1g	299	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(S); elpi z_report "occ.1g" "300" ltac_term:(G)) | idtac "SSR	occ.1g	300	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S (S X) + _ /\ _); elpi z_report "occ.1g" "301" ltac_term:(G)) | idtac "SSR	occ.1g	301	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = S (S X) + _ /\ _); elpi z_report "occ.1g" "302" ltac_term:(G)) | idtac "SSR	occ.1g	302	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) + _); elpi z_report "occ.1g" "303" ltac_term:(G)) | idtac "SSR	occ.1g	303	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S (S X) + _); elpi z_report "occ.1g" "304" ltac_term:(G)) | idtac "SSR	occ.1g	304	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(0); elpi z_report "occ.1g" "305" ltac_term:(G)) | idtac "SSR	occ.1g	305	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(0); elpi z_report "occ.1g" "306" ltac_term:(G)) | idtac "SSR	occ.1g	306	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S (S X) + _); elpi z_report "occ.1g" "307" ltac_term:(G)) | idtac "SSR	occ.1g	307	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ = S (S X) + _); elpi z_report "occ.1g" "308" ltac_term:(G)) | idtac "SSR	occ.1g	308	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = _ + X /\ _); elpi z_report "occ.1g" "309" ltac_term:(G)) | idtac "SSR	occ.1g	309	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S m) = _ + X /\ _); elpi z_report "occ.1g" "310" ltac_term:(G)) | idtac "SSR	occ.1g	310	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (m); elpi z_report "occ.1g" "311" ltac_term:(G)) | idtac "SSR	occ.1g	311	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 2 + X); elpi z_report "occ.1g" "312" ltac_term:(G)) | idtac "SSR	occ.1g	312	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S m) = _ + X); elpi z_report "occ.1g" "313" ltac_term:(G)) | idtac "SSR	occ.1g	313	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(m); elpi z_report "occ.1g" "314" ltac_term:(G)) | idtac "SSR	occ.1g	314	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(m); elpi z_report "occ.1g" "315" ltac_term:(G)) | idtac "SSR	occ.1g	315	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in 2 + X); elpi z_report "occ.1g" "316" ltac_term:(G)) | idtac "SSR	occ.1g	316	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S (S m) = _ + X); elpi z_report "occ.1g" "317" ltac_term:(G)) | idtac "SSR	occ.1g	317	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 = _); elpi z_report "occ.1g" "318" ltac_term:(G)) | idtac "SSR	occ.1g	318	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "occ.1g" "319" ltac_term:(G)) | idtac "SSR	occ.1g	319	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ X); elpi z_report "occ.1g" "320" ltac_term:(G)) | idtac "SSR	occ.1g	320	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 = _ in X in _ /\ X); elpi z_report "occ.1g" "321" ltac_term:(G)) | idtac "SSR	occ.1g	321	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ _ /\ X); elpi z_report "occ.1g" "322" ltac_term:(G)) | idtac "SSR	occ.1g	322	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S m) = _ /\ X); elpi z_report "occ.1g" "323" ltac_term:(G)) | idtac "SSR	occ.1g	323	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 = 1 + 1); elpi z_report "occ.1g" "324" ltac_term:(G)) | idtac "SSR	occ.1g	324	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "occ.1g" "325" ltac_term:(G)) | idtac "SSR	occ.1g	325	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(@eq); elpi z_report "occ.1g" "326" ltac_term:(G)) | idtac "SSR	occ.1g	326	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(@eq); elpi z_report "occ.1g" "327" ltac_term:(G)) | idtac "SSR	occ.1g	327	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "occ.1g" "328" ltac_term:(G)) | idtac "SSR	occ.1g	328	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "occ.1g" "329" ltac_term:(G)) | idtac "SSR	occ.1g	329	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "occ.1g" "330" ltac_term:(G)) | idtac "SSR	occ.1g	330	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 as X in X = _); elpi z_report "occ.1g" "331" ltac_term:(G)) | idtac "SSR	occ.1g	331	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "occ.1g" "332" ltac_term:(G)) | idtac "SSR	occ.1g	332	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = 1 + _); elpi z_report "occ.1g" "333" ltac_term:(G)) | idtac "SSR	occ.1g	333	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ X = _); elpi z_report "occ.1g" "334" ltac_term:(G)) | idtac "SSR	occ.1g	334	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ /\ _ /\ X); elpi z_report "occ.1g" "335" ltac_term:(G)) | idtac "SSR	occ.1g	335	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ X = _); elpi z_report "occ.1g" "336" ltac_term:(G)) | idtac "SSR	occ.1g	336	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ /\ X = _); elpi z_report "occ.1g" "337" ltac_term:(G)) | idtac "SSR	occ.1g	337	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in S (S m) = _ /\ X); elpi z_report "occ.1g" "338" ltac_term:(G)) | idtac "SSR	occ.1g	338	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2); elpi z_report "occ.1g" "339" ltac_term:(G)) | idtac "SSR	occ.1g	339	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 in X in _ /\ X); elpi z_report "occ.1g" "340" ltac_term:(G)) | idtac "SSR	occ.1g	340	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(2); elpi z_report "occ.1g" "341" ltac_term:(G)) | idtac "SSR	occ.1g	341	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(2); elpi z_report "occ.1g" "342" ltac_term:(G)) | idtac "SSR	occ.1g	342	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(2 in X in _ /\ X); elpi z_report "occ.1g" "343" ltac_term:(G)) | idtac "SSR	occ.1g	343	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(S); elpi z_report "occ.1g" "344" ltac_term:(G)) | idtac "SSR	occ.1g	344	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(S); elpi z_report "occ.1g" "345" ltac_term:(G)) | idtac "SSR	occ.1g	345	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X = _); elpi z_report "occ.1g" "346" ltac_term:(G)) | idtac "SSR	occ.1g	346	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ /\ X = _); elpi z_report "occ.1g" "347" ltac_term:(G)) | idtac "SSR	occ.1g	347	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ S X = _); elpi z_report "occ.1g" "348" ltac_term:(G)) | idtac "SSR	occ.1g	348	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = 1 + _); elpi z_report "occ.1g" "349" ltac_term:(G)) | idtac "SSR	occ.1g	349	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X = 1 + _); elpi z_report "occ.1g" "350" ltac_term:(G)) | idtac "SSR	occ.1g	350	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ S X = _); elpi z_report "occ.1g" "351" ltac_term:(G)) | idtac "SSR	occ.1g	351	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ S X = _); elpi z_report "occ.1g" "352" ltac_term:(G)) | idtac "SSR	occ.1g	352	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ /\ S X = _); elpi z_report "occ.1g" "353" ltac_term:(G)) | idtac "SSR	occ.1g	353	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in S X); elpi z_report "occ.1g" "354" ltac_term:(G)) | idtac "SSR	occ.1g	354	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(1); elpi z_report "occ.1g" "355" ltac_term:(G)) | idtac "SSR	occ.1g	355	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(1); elpi z_report "occ.1g" "356" ltac_term:(G)) | idtac "SSR	occ.1g	356	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 as X in S X); elpi z_report "occ.1g" "357" ltac_term:(G)) | idtac "SSR	occ.1g	357	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in _ /\ X); elpi z_report "occ.1g" "358" ltac_term:(G)) | idtac "SSR	occ.1g	358	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in _ /\ _ /\ X); elpi z_report "occ.1g" "359" ltac_term:(G)) | idtac "SSR	occ.1g	359	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 in X in S (S m) = _ /\ X); elpi z_report "occ.1g" "360" ltac_term:(G)) | idtac "SSR	occ.1g	360	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(S); elpi z_report "occ.1g" "361" ltac_term:(G)) | idtac "SSR	occ.1g	361	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(S); elpi z_report "occ.1g" "362" ltac_term:(G)) | idtac "SSR	occ.1g	362	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ S (S X) = _); elpi z_report "occ.1g" "363" ltac_term:(G)) | idtac "SSR	occ.1g	363	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) = 1 + _); elpi z_report "occ.1g" "364" ltac_term:(G)) | idtac "SSR	occ.1g	364	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ S (S X) = _); elpi z_report "occ.1g" "365" ltac_term:(G)) | idtac "SSR	occ.1g	365	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(0); elpi z_report "occ.1g" "366" ltac_term:(G)) | idtac "SSR	occ.1g	366	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(0); elpi z_report "occ.1g" "367" ltac_term:(G)) | idtac "SSR	occ.1g	367	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 2 = X); elpi z_report "occ.1g" "368" ltac_term:(G)) | idtac "SSR	occ.1g	368	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "occ.1g" "369" ltac_term:(G)) | idtac "SSR	occ.1g	369	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _ as X in _ = X); elpi z_report "occ.1g" "370" ltac_term:(G)) | idtac "SSR	occ.1g	370	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _ in X in _ /\ X); elpi z_report "occ.1g" "371" ltac_term:(G)) | idtac "SSR	occ.1g	371	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ /\ _ = X); elpi z_report "occ.1g" "372" ltac_term:(G)) | idtac "SSR	occ.1g	372	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ _ /\ X); elpi z_report "occ.1g" "373" ltac_term:(G)) | idtac "SSR	occ.1g	373	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ _ = X); elpi z_report "occ.1g" "374" ltac_term:(G)) | idtac "SSR	occ.1g	374	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ /\ _ /\ _ = X); elpi z_report "occ.1g" "375" ltac_term:(G)) | idtac "SSR	occ.1g	375	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in S (S m) = _ /\ X); elpi z_report "occ.1g" "376" ltac_term:(G)) | idtac "SSR	occ.1g	376	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _); elpi z_report "occ.1g" "377" ltac_term:(G)) | idtac "SSR	occ.1g	377	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 + _); elpi z_report "occ.1g" "378" ltac_term:(G)) | idtac "SSR	occ.1g	378	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 + 1); elpi z_report "occ.1g" "379" ltac_term:(G)) | idtac "SSR	occ.1g	379	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "occ.1g" "380" ltac_term:(G)) | idtac "SSR	occ.1g	380	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Nat.add); elpi z_report "occ.1g" "381" ltac_term:(G)) | idtac "SSR	occ.1g	381	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Nat.add); elpi z_report "occ.1g" "382" ltac_term:(G)) | idtac "SSR	occ.1g	382	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + 1); elpi z_report "occ.1g" "383" ltac_term:(G)) | idtac "SSR	occ.1g	383	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in _ = X + _); elpi z_report "occ.1g" "384" ltac_term:(G)) | idtac "SSR	occ.1g	384	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X + _); elpi z_report "occ.1g" "385" ltac_term:(G)) | idtac "SSR	occ.1g	385	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ = X + _); elpi z_report "occ.1g" "386" ltac_term:(G)) | idtac "SSR	occ.1g	386	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ _ = X + _); elpi z_report "occ.1g" "387" ltac_term:(G)) | idtac "SSR	occ.1g	387	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ /\ _ = X + _); elpi z_report "occ.1g" "388" ltac_term:(G)) | idtac "SSR	occ.1g	388	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + 1); elpi z_report "occ.1g" "389" ltac_term:(G)) | idtac "SSR	occ.1g	389	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 as X in X + _); elpi z_report "occ.1g" "390" ltac_term:(G)) | idtac "SSR	occ.1g	390	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(1); elpi z_report "occ.1g" "391" ltac_term:(G)) | idtac "SSR	occ.1g	391	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(1); elpi z_report "occ.1g" "392" ltac_term:(G)) | idtac "SSR	occ.1g	392	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X + 1); elpi z_report "occ.1g" "393" ltac_term:(G)) | idtac "SSR	occ.1g	393	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 as X in X + _); elpi z_report "occ.1g" "394" ltac_term:(G)) | idtac "SSR	occ.1g	394	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in _ /\ X); elpi z_report "occ.1g" "395" ltac_term:(G)) | idtac "SSR	occ.1g	395	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in 2 = X); elpi z_report "occ.1g" "396" ltac_term:(G)) | idtac "SSR	occ.1g	396	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in _ /\ _ /\ X); elpi z_report "occ.1g" "397" ltac_term:(G)) | idtac "SSR	occ.1g	397	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in _ /\ _ = X); elpi z_report "occ.1g" "398" ltac_term:(G)) | idtac "SSR	occ.1g	398	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 in X in S (S m) = _ /\ X); elpi z_report "occ.1g" "399" ltac_term:(G)) | idtac "SSR	occ.1g	399	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {11}(S); elpi z_report "occ.1g" "400" ltac_term:(G)) | idtac "SSR	occ.1g	400	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {11}(S); elpi z_report "occ.1g" "401" ltac_term:(G)) | idtac "SSR	occ.1g	401	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X + 1); elpi z_report "occ.1g" "402" ltac_term:(G)) | idtac "SSR	occ.1g	402	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = S X + _); elpi z_report "occ.1g" "403" ltac_term:(G)) | idtac "SSR	occ.1g	403	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ _ = S X + _); elpi z_report "occ.1g" "404" ltac_term:(G)) | idtac "SSR	occ.1g	404	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + 1); elpi z_report "occ.1g" "405" ltac_term:(G)) | idtac "SSR	occ.1g	405	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(0); elpi z_report "occ.1g" "406" ltac_term:(G)) | idtac "SSR	occ.1g	406	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(0); elpi z_report "occ.1g" "407" ltac_term:(G)) | idtac "SSR	occ.1g	407	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X + 1); elpi z_report "occ.1g" "408" ltac_term:(G)) | idtac "SSR	occ.1g	408	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = 1 + X); elpi z_report "occ.1g" "409" ltac_term:(G)) | idtac "SSR	occ.1g	409	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = _ + X); elpi z_report "occ.1g" "410" ltac_term:(G)) | idtac "SSR	occ.1g	410	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = _ + X); elpi z_report "occ.1g" "411" ltac_term:(G)) | idtac "SSR	occ.1g	411	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ = _ + X); elpi z_report "occ.1g" "412" ltac_term:(G)) | idtac "SSR	occ.1g	412	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ _ = _ + X); elpi z_report "occ.1g" "413" ltac_term:(G)) | idtac "SSR	occ.1g	413	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ /\ _ /\ _ = _ + X); elpi z_report "occ.1g" "414" ltac_term:(G)) | idtac "SSR	occ.1g	414	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "occ.1g" "415" ltac_term:(G)) | idtac "SSR	occ.1g	415	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + X); elpi z_report "occ.1g" "416" ltac_term:(G)) | idtac "SSR	occ.1g	416	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ /\ X); elpi z_report "occ.1g" "417" ltac_term:(G)) | idtac "SSR	occ.1g	417	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X); elpi z_report "occ.1g" "418" ltac_term:(G)) | idtac "SSR	occ.1g	418	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 2 = X); elpi z_report "occ.1g" "419" ltac_term:(G)) | idtac "SSR	occ.1g	419	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ /\ _ /\ X); elpi z_report "occ.1g" "420" ltac_term:(G)) | idtac "SSR	occ.1g	420	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ /\ _ = X); elpi z_report "occ.1g" "421" ltac_term:(G)) | idtac "SSR	occ.1g	421	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in S (S m) = _ /\ X); elpi z_report "occ.1g" "422" ltac_term:(G)) | idtac "SSR	occ.1g	422	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(1); elpi z_report "occ.1g" "423" ltac_term:(G)) | idtac "SSR	occ.1g	423	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(1); elpi z_report "occ.1g" "424" ltac_term:(G)) | idtac "SSR	occ.1g	424	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in 1 + X); elpi z_report "occ.1g" "425" ltac_term:(G)) | idtac "SSR	occ.1g	425	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(1 in X in _ /\ X); elpi z_report "occ.1g" "426" ltac_term:(G)) | idtac "SSR	occ.1g	426	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in _ + X); elpi z_report "occ.1g" "427" ltac_term:(G)) | idtac "SSR	occ.1g	427	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in 2 = X); elpi z_report "occ.1g" "428" ltac_term:(G)) | idtac "SSR	occ.1g	428	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in _ /\ _ /\ X); elpi z_report "occ.1g" "429" ltac_term:(G)) | idtac "SSR	occ.1g	429	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in _ /\ _ = X); elpi z_report "occ.1g" "430" ltac_term:(G)) | idtac "SSR	occ.1g	430	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 in X in S (S m) = _ /\ X); elpi z_report "occ.1g" "431" ltac_term:(G)) | idtac "SSR	occ.1g	431	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "occ.1g" "432" ltac_term:(G)) | idtac "SSR	occ.1g	432	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {12}(S); elpi z_report "occ.1g" "433" ltac_term:(G)) | idtac "SSR	occ.1g	433	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {12}(S); elpi z_report "occ.1g" "434" ltac_term:(G)) | idtac "SSR	occ.1g	434	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + S X); elpi z_report "occ.1g" "435" ltac_term:(G)) | idtac "SSR	occ.1g	435	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = _ + S X); elpi z_report "occ.1g" "436" ltac_term:(G)) | idtac "SSR	occ.1g	436	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ /\ _ = _ + S X); elpi z_report "occ.1g" "437" ltac_term:(G)) | idtac "SSR	occ.1g	437	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "occ.1g" "438" ltac_term:(G)) | idtac "SSR	occ.1g	438	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X); elpi z_report "occ.1g" "439" ltac_term:(G)) | idtac "SSR	occ.1g	439	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(0); elpi z_report "occ.1g" "440" ltac_term:(G)) | idtac "SSR	occ.1g	440	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(0); elpi z_report "occ.1g" "441" ltac_term:(G)) | idtac "SSR	occ.1g	441	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ + S X); elpi z_report "occ.1g" "442" ltac_term:(G)) | idtac "SSR	occ.1g	442	error" ].
Abort.

Definition twice (n : nat) := n + n.
Goal forall n : nat, twice n = n + n /\ twice (n + n) = twice n + twice n.
intros n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _); elpi z_report "occ.2" "1" ltac_term:(G)) | idtac "SSR	occ.2	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "occ.2" "2" ltac_term:(G)) | idtac "SSR	occ.2	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n + n); elpi z_report "occ.2" "3" ltac_term:(G)) | idtac "SSR	occ.2	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice n); elpi z_report "occ.2" "4" ltac_term:(G)) | idtac "SSR	occ.2	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice _); elpi z_report "occ.2" "5" ltac_term:(G)) | idtac "SSR	occ.2	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice (_ + _)); elpi z_report "occ.2" "6" ltac_term:(G)) | idtac "SSR	occ.2	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n); elpi z_report "occ.2" "7" ltac_term:(G)) | idtac "SSR	occ.2	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "occ.2g" "1" ltac_term:(G)) | idtac "SSR	occ.2g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice n = n + n /\ twice (n + n) = twice n + twice n); elpi z_report "occ.2g" "2" ltac_term:(G)) | idtac "SSR	occ.2g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "occ.2g" "3" ltac_term:(G)) | idtac "SSR	occ.2g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "occ.2g" "4" ltac_term:(G)) | idtac "SSR	occ.2g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "occ.2g" "5" ltac_term:(G)) | idtac "SSR	occ.2g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "occ.2g" "6" ltac_term:(G)) | idtac "SSR	occ.2g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "occ.2g" "7" ltac_term:(G)) | idtac "SSR	occ.2g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice n = n + n); elpi z_report "occ.2g" "8" ltac_term:(G)) | idtac "SSR	occ.2g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "occ.2g" "9" ltac_term:(G)) | idtac "SSR	occ.2g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "occ.2g" "10" ltac_term:(G)) | idtac "SSR	occ.2g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "occ.2g" "11" ltac_term:(G)) | idtac "SSR	occ.2g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "occ.2g" "12" ltac_term:(G)) | idtac "SSR	occ.2g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "occ.2g" "13" ltac_term:(G)) | idtac "SSR	occ.2g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in X = _); elpi z_report "occ.2g" "14" ltac_term:(G)) | idtac "SSR	occ.2g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ in X in X /\ _); elpi z_report "occ.2g" "15" ltac_term:(G)) | idtac "SSR	occ.2g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "occ.2g" "16" ltac_term:(G)) | idtac "SSR	occ.2g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in X = _ /\ _); elpi z_report "occ.2g" "17" ltac_term:(G)) | idtac "SSR	occ.2g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _); elpi z_report "occ.2g" "18" ltac_term:(G)) | idtac "SSR	occ.2g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice _); elpi z_report "occ.2g" "19" ltac_term:(G)) | idtac "SSR	occ.2g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice n); elpi z_report "occ.2g" "20" ltac_term:(G)) | idtac "SSR	occ.2g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice); elpi z_report "occ.2g" "21" ltac_term:(G)) | idtac "SSR	occ.2g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice); elpi z_report "occ.2g" "22" ltac_term:(G)) | idtac "SSR	occ.2g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice X = _); elpi z_report "occ.2g" "23" ltac_term:(G)) | idtac "SSR	occ.2g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice X = _ /\ _); elpi z_report "occ.2g" "24" ltac_term:(G)) | idtac "SSR	occ.2g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice X); elpi z_report "occ.2g" "25" ltac_term:(G)) | idtac "SSR	occ.2g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "occ.2g" "26" ltac_term:(G)) | idtac "SSR	occ.2g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "occ.2g" "27" ltac_term:(G)) | idtac "SSR	occ.2g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in twice X); elpi z_report "occ.2g" "28" ltac_term:(G)) | idtac "SSR	occ.2g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "occ.2g" "29" ltac_term:(G)) | idtac "SSR	occ.2g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "occ.2g" "30" ltac_term:(G)) | idtac "SSR	occ.2g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ _); elpi z_report "occ.2g" "31" ltac_term:(G)) | idtac "SSR	occ.2g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "occ.2g" "32" ltac_term:(G)) | idtac "SSR	occ.2g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X /\ _); elpi z_report "occ.2g" "33" ltac_term:(G)) | idtac "SSR	occ.2g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + _); elpi z_report "occ.2g" "34" ltac_term:(G)) | idtac "SSR	occ.2g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n + n); elpi z_report "occ.2g" "35" ltac_term:(G)) | idtac "SSR	occ.2g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "occ.2g" "36" ltac_term:(G)) | idtac "SSR	occ.2g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "occ.2g" "37" ltac_term:(G)) | idtac "SSR	occ.2g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "occ.2g" "38" ltac_term:(G)) | idtac "SSR	occ.2g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ /\ _); elpi z_report "occ.2g" "39" ltac_term:(G)) | idtac "SSR	occ.2g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "occ.2g" "40" ltac_term:(G)) | idtac "SSR	occ.2g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "occ.2g" "41" ltac_term:(G)) | idtac "SSR	occ.2g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + _); elpi z_report "occ.2g" "42" ltac_term:(G)) | idtac "SSR	occ.2g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "occ.2g" "43" ltac_term:(G)) | idtac "SSR	occ.2g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X /\ _); elpi z_report "occ.2g" "44" ltac_term:(G)) | idtac "SSR	occ.2g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "occ.2g" "45" ltac_term:(G)) | idtac "SSR	occ.2g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "occ.2g" "46" ltac_term:(G)) | idtac "SSR	occ.2g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ + X); elpi z_report "occ.2g" "47" ltac_term:(G)) | idtac "SSR	occ.2g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "occ.2g" "48" ltac_term:(G)) | idtac "SSR	occ.2g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "occ.2g" "49" ltac_term:(G)) | idtac "SSR	occ.2g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = twice n + _); elpi z_report "occ.2g" "50" ltac_term:(G)) | idtac "SSR	occ.2g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice (n + n) = twice n + twice n); elpi z_report "occ.2g" "51" ltac_term:(G)) | idtac "SSR	occ.2g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "occ.2g" "52" ltac_term:(G)) | idtac "SSR	occ.2g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "occ.2g" "53" ltac_term:(G)) | idtac "SSR	occ.2g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "occ.2g" "54" ltac_term:(G)) | idtac "SSR	occ.2g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "occ.2g" "55" ltac_term:(G)) | idtac "SSR	occ.2g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "occ.2g" "56" ltac_term:(G)) | idtac "SSR	occ.2g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "occ.2g" "57" ltac_term:(G)) | idtac "SSR	occ.2g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ in X in _ /\ X); elpi z_report "occ.2g" "58" ltac_term:(G)) | idtac "SSR	occ.2g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "occ.2g" "59" ltac_term:(G)) | idtac "SSR	occ.2g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in _ /\ X = _); elpi z_report "occ.2g" "60" ltac_term:(G)) | idtac "SSR	occ.2g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice (n + n)); elpi z_report "occ.2g" "61" ltac_term:(G)) | idtac "SSR	occ.2g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = twice n + _); elpi z_report "occ.2g" "62" ltac_term:(G)) | idtac "SSR	occ.2g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice (n + n) as X in X = _); elpi z_report "occ.2g" "63" ltac_term:(G)) | idtac "SSR	occ.2g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice (n + n)); elpi z_report "occ.2g" "64" ltac_term:(G)) | idtac "SSR	occ.2g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice); elpi z_report "occ.2g" "65" ltac_term:(G)) | idtac "SSR	occ.2g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice); elpi z_report "occ.2g" "66" ltac_term:(G)) | idtac "SSR	occ.2g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ X); elpi z_report "occ.2g" "67" ltac_term:(G)) | idtac "SSR	occ.2g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in twice X); elpi z_report "occ.2g" "68" ltac_term:(G)) | idtac "SSR	occ.2g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ X = _); elpi z_report "occ.2g" "69" ltac_term:(G)) | idtac "SSR	occ.2g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in twice X = _); elpi z_report "occ.2g" "70" ltac_term:(G)) | idtac "SSR	occ.2g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ twice X = _); elpi z_report "occ.2g" "71" ltac_term:(G)) | idtac "SSR	occ.2g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ /\ twice X = _); elpi z_report "occ.2g" "72" ltac_term:(G)) | idtac "SSR	occ.2g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X = twice n + _); elpi z_report "occ.2g" "73" ltac_term:(G)) | idtac "SSR	occ.2g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice X = twice n + _); elpi z_report "occ.2g" "74" ltac_term:(G)) | idtac "SSR	occ.2g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "occ.2g" "75" ltac_term:(G)) | idtac "SSR	occ.2g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + _); elpi z_report "occ.2g" "76" ltac_term:(G)) | idtac "SSR	occ.2g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n + n); elpi z_report "occ.2g" "77" ltac_term:(G)) | idtac "SSR	occ.2g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "occ.2g" "78" ltac_term:(G)) | idtac "SSR	occ.2g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "occ.2g" "79" ltac_term:(G)) | idtac "SSR	occ.2g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice (X + _)); elpi z_report "occ.2g" "80" ltac_term:(G)) | idtac "SSR	occ.2g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice (X + _) = _); elpi z_report "occ.2g" "81" ltac_term:(G)) | idtac "SSR	occ.2g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ twice (X + _) = _); elpi z_report "occ.2g" "82" ltac_term:(G)) | idtac "SSR	occ.2g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "occ.2g" "83" ltac_term:(G)) | idtac "SSR	occ.2g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "occ.2g" "84" ltac_term:(G)) | idtac "SSR	occ.2g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "occ.2g" "85" ltac_term:(G)) | idtac "SSR	occ.2g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X + _); elpi z_report "occ.2g" "86" ltac_term:(G)) | idtac "SSR	occ.2g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice (_ + X)); elpi z_report "occ.2g" "87" ltac_term:(G)) | idtac "SSR	occ.2g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice (_ + X) = _); elpi z_report "occ.2g" "88" ltac_term:(G)) | idtac "SSR	occ.2g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ twice (_ + X) = _); elpi z_report "occ.2g" "89" ltac_term:(G)) | idtac "SSR	occ.2g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "occ.2g" "90" ltac_term:(G)) | idtac "SSR	occ.2g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(n); elpi z_report "occ.2g" "91" ltac_term:(G)) | idtac "SSR	occ.2g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(n); elpi z_report "occ.2g" "92" ltac_term:(G)) | idtac "SSR	occ.2g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ + X); elpi z_report "occ.2g" "93" ltac_term:(G)) | idtac "SSR	occ.2g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "occ.2g" "94" ltac_term:(G)) | idtac "SSR	occ.2g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice n + _); elpi z_report "occ.2g" "95" ltac_term:(G)) | idtac "SSR	occ.2g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ /\ _ = X); elpi z_report "occ.2g" "96" ltac_term:(G)) | idtac "SSR	occ.2g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice n + _ as X in _ = X); elpi z_report "occ.2g" "97" ltac_term:(G)) | idtac "SSR	occ.2g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice n + _ in X in _ /\ X); elpi z_report "occ.2g" "98" ltac_term:(G)) | idtac "SSR	occ.2g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice (n + n) = X); elpi z_report "occ.2g" "99" ltac_term:(G)) | idtac "SSR	occ.2g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice n + twice n); elpi z_report "occ.2g" "100" ltac_term:(G)) | idtac "SSR	occ.2g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "occ.2g" "101" ltac_term:(G)) | idtac "SSR	occ.2g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "occ.2g" "102" ltac_term:(G)) | idtac "SSR	occ.2g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "occ.2g" "103" ltac_term:(G)) | idtac "SSR	occ.2g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in X + _); elpi z_report "occ.2g" "104" ltac_term:(G)) | idtac "SSR	occ.2g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + twice n); elpi z_report "occ.2g" "105" ltac_term:(G)) | idtac "SSR	occ.2g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in _ = X + _); elpi z_report "occ.2g" "106" ltac_term:(G)) | idtac "SSR	occ.2g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X + _); elpi z_report "occ.2g" "107" ltac_term:(G)) | idtac "SSR	occ.2g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + twice n); elpi z_report "occ.2g" "108" ltac_term:(G)) | idtac "SSR	occ.2g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in _ /\ _ = X + _); elpi z_report "occ.2g" "109" ltac_term:(G)) | idtac "SSR	occ.2g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice n); elpi z_report "occ.2g" "110" ltac_term:(G)) | idtac "SSR	occ.2g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice n); elpi z_report "occ.2g" "111" ltac_term:(G)) | idtac "SSR	occ.2g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice n in X in _ /\ X); elpi z_report "occ.2g" "112" ltac_term:(G)) | idtac "SSR	occ.2g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice _ in X in _ /\ _ = X); elpi z_report "occ.2g" "113" ltac_term:(G)) | idtac "SSR	occ.2g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(twice _ in X in twice (n + n) = X); elpi z_report "occ.2g" "114" ltac_term:(G)) | idtac "SSR	occ.2g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(twice); elpi z_report "occ.2g" "115" ltac_term:(G)) | idtac "SSR	occ.2g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(twice); elpi z_report "occ.2g" "116" ltac_term:(G)) | idtac "SSR	occ.2g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice X + _); elpi z_report "occ.2g" "117" ltac_term:(G)) | idtac "SSR	occ.2g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = twice X + _); elpi z_report "occ.2g" "118" ltac_term:(G)) | idtac "SSR	occ.2g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = twice X + _); elpi z_report "occ.2g" "119" ltac_term:(G)) | idtac "SSR	occ.2g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(n); elpi z_report "occ.2g" "120" ltac_term:(G)) | idtac "SSR	occ.2g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(n); elpi z_report "occ.2g" "121" ltac_term:(G)) | idtac "SSR	occ.2g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in _ + X); elpi z_report "occ.2g" "122" ltac_term:(G)) | idtac "SSR	occ.2g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in twice n + X); elpi z_report "occ.2g" "123" ltac_term:(G)) | idtac "SSR	occ.2g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in _ = _ + X); elpi z_report "occ.2g" "124" ltac_term:(G)) | idtac "SSR	occ.2g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = _ + X); elpi z_report "occ.2g" "125" ltac_term:(G)) | idtac "SSR	occ.2g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = twice n + X); elpi z_report "occ.2g" "126" ltac_term:(G)) | idtac "SSR	occ.2g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ as X in _ /\ _ = _ + X); elpi z_report "occ.2g" "127" ltac_term:(G)) | idtac "SSR	occ.2g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice n); elpi z_report "occ.2g" "128" ltac_term:(G)) | idtac "SSR	occ.2g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice n in X in _ /\ X); elpi z_report "occ.2g" "129" ltac_term:(G)) | idtac "SSR	occ.2g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ in X in _ /\ _ = X); elpi z_report "occ.2g" "130" ltac_term:(G)) | idtac "SSR	occ.2g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice _ in X in twice (n + n) = X); elpi z_report "occ.2g" "131" ltac_term:(G)) | idtac "SSR	occ.2g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(twice n); elpi z_report "occ.2g" "132" ltac_term:(G)) | idtac "SSR	occ.2g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(twice n); elpi z_report "occ.2g" "133" ltac_term:(G)) | idtac "SSR	occ.2g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice n in X in _ /\ X); elpi z_report "occ.2g" "134" ltac_term:(G)) | idtac "SSR	occ.2g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice _ in X in _ /\ _ = X); elpi z_report "occ.2g" "135" ltac_term:(G)) | idtac "SSR	occ.2g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(twice _ in X in twice (n + n) = X); elpi z_report "occ.2g" "136" ltac_term:(G)) | idtac "SSR	occ.2g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (twice); elpi z_report "occ.2g" "137" ltac_term:(G)) | idtac "SSR	occ.2g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(twice); elpi z_report "occ.2g" "138" ltac_term:(G)) | idtac "SSR	occ.2g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(twice); elpi z_report "occ.2g" "139" ltac_term:(G)) | idtac "SSR	occ.2g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + twice X); elpi z_report "occ.2g" "140" ltac_term:(G)) | idtac "SSR	occ.2g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + twice X); elpi z_report "occ.2g" "141" ltac_term:(G)) | idtac "SSR	occ.2g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = _ + twice X); elpi z_report "occ.2g" "142" ltac_term:(G)) | idtac "SSR	occ.2g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "occ.2g" "143" ltac_term:(G)) | idtac "SSR	occ.2g	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(n); elpi z_report "occ.2g" "144" ltac_term:(G)) | idtac "SSR	occ.2g	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(n); elpi z_report "occ.2g" "145" ltac_term:(G)) | idtac "SSR	occ.2g	145	error" ].
Abort.

(* keyed matching and conversion: phase 1 without reduction, phase 2 with
   it (paper, Ex. 10) *)
Goal forall n m : nat, n + 2 * m = m + (m + n) /\ 0 + n = n.
intros n m.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (_ + _)); elpi z_report "conv.1" "1" ltac_term:(G)) | idtac "SSR	conv.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (m + 0)); elpi z_report "conv.1" "2" ltac_term:(G)) | idtac "SSR	conv.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n + _); elpi z_report "conv.1" "3" ltac_term:(G)) | idtac "SSR	conv.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * m); elpi z_report "conv.1" "4" ltac_term:(G)) | idtac "SSR	conv.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 * _); elpi z_report "conv.1" "5" ltac_term:(G)) | idtac "SSR	conv.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _); elpi z_report "conv.1" "6" ltac_term:(G)) | idtac "SSR	conv.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n); elpi z_report "conv.1" "7" ltac_term:(G)) | idtac "SSR	conv.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n + (m + _)); elpi z_report "conv.1" "8" ltac_term:(G)) | idtac "SSR	conv.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in n + X); elpi z_report "conv.1" "9" ltac_term:(G)) | idtac "SSR	conv.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "conv.1g" "1" ltac_term:(G)) | idtac "SSR	conv.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n + 2 * m = m + (m + n) /\ 0 + n = n); elpi z_report "conv.1g" "2" ltac_term:(G)) | idtac "SSR	conv.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "conv.1g" "3" ltac_term:(G)) | idtac "SSR	conv.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "conv.1g" "4" ltac_term:(G)) | idtac "SSR	conv.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "conv.1g" "5" ltac_term:(G)) | idtac "SSR	conv.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "conv.1g" "6" ltac_term:(G)) | idtac "SSR	conv.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "conv.1g" "7" ltac_term:(G)) | idtac "SSR	conv.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n + 2 * m = m + (m + n)); elpi z_report "conv.1g" "8" ltac_term:(G)) | idtac "SSR	conv.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "conv.1g" "9" ltac_term:(G)) | idtac "SSR	conv.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "conv.1g" "10" ltac_term:(G)) | idtac "SSR	conv.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "conv.1g" "11" ltac_term:(G)) | idtac "SSR	conv.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "conv.1g" "12" ltac_term:(G)) | idtac "SSR	conv.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "conv.1g" "13" ltac_term:(G)) | idtac "SSR	conv.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "conv.1g" "14" ltac_term:(G)) | idtac "SSR	conv.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "conv.1g" "15" ltac_term:(G)) | idtac "SSR	conv.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ _); elpi z_report "conv.1g" "16" ltac_term:(G)) | idtac "SSR	conv.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "conv.1g" "17" ltac_term:(G)) | idtac "SSR	conv.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _ /\ _); elpi z_report "conv.1g" "18" ltac_term:(G)) | idtac "SSR	conv.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n + 2 * m); elpi z_report "conv.1g" "19" ltac_term:(G)) | idtac "SSR	conv.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "conv.1g" "20" ltac_term:(G)) | idtac "SSR	conv.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "conv.1g" "21" ltac_term:(G)) | idtac "SSR	conv.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "conv.1g" "22" ltac_term:(G)) | idtac "SSR	conv.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "conv.1g" "23" ltac_term:(G)) | idtac "SSR	conv.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _ /\ _); elpi z_report "conv.1g" "24" ltac_term:(G)) | idtac "SSR	conv.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "conv.1g" "25" ltac_term:(G)) | idtac "SSR	conv.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "conv.1g" "26" ltac_term:(G)) | idtac "SSR	conv.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "conv.1g" "27" ltac_term:(G)) | idtac "SSR	conv.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "conv.1g" "28" ltac_term:(G)) | idtac "SSR	conv.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X); elpi z_report "conv.1g" "29" ltac_term:(G)) | idtac "SSR	conv.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _); elpi z_report "conv.1g" "30" ltac_term:(G)) | idtac "SSR	conv.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X /\ _); elpi z_report "conv.1g" "31" ltac_term:(G)) | idtac "SSR	conv.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "conv.1g" "32" ltac_term:(G)) | idtac "SSR	conv.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X = _); elpi z_report "conv.1g" "33" ltac_term:(G)) | idtac "SSR	conv.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _ /\ _); elpi z_report "conv.1g" "34" ltac_term:(G)) | idtac "SSR	conv.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _ /\ _); elpi z_report "conv.1g" "35" ltac_term:(G)) | idtac "SSR	conv.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X = _ /\ _); elpi z_report "conv.1g" "36" ltac_term:(G)) | idtac "SSR	conv.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 * m); elpi z_report "conv.1g" "37" ltac_term:(G)) | idtac "SSR	conv.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.mul); elpi z_report "conv.1g" "38" ltac_term:(G)) | idtac "SSR	conv.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.mul); elpi z_report "conv.1g" "39" ltac_term:(G)) | idtac "SSR	conv.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "conv.1g" "40" ltac_term:(G)) | idtac "SSR	conv.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "conv.1g" "41" ltac_term:(G)) | idtac "SSR	conv.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X * _); elpi z_report "conv.1g" "42" ltac_term:(G)) | idtac "SSR	conv.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "conv.1g" "43" ltac_term:(G)) | idtac "SSR	conv.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X); elpi z_report "conv.1g" "44" ltac_term:(G)) | idtac "SSR	conv.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X /\ _); elpi z_report "conv.1g" "45" ltac_term:(G)) | idtac "SSR	conv.1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _); elpi z_report "conv.1g" "46" ltac_term:(G)) | idtac "SSR	conv.1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X * _); elpi z_report "conv.1g" "47" ltac_term:(G)) | idtac "SSR	conv.1g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X = _); elpi z_report "conv.1g" "48" ltac_term:(G)) | idtac "SSR	conv.1g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _ /\ _); elpi z_report "conv.1g" "49" ltac_term:(G)) | idtac "SSR	conv.1g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _ = _); elpi z_report "conv.1g" "50" ltac_term:(G)) | idtac "SSR	conv.1g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X * _ = _); elpi z_report "conv.1g" "51" ltac_term:(G)) | idtac "SSR	conv.1g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _ = _ /\ _); elpi z_report "conv.1g" "52" ltac_term:(G)) | idtac "SSR	conv.1g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X * _ = _ /\ _); elpi z_report "conv.1g" "53" ltac_term:(G)) | idtac "SSR	conv.1g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2); elpi z_report "conv.1g" "54" ltac_term:(G)) | idtac "SSR	conv.1g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "conv.1g" "55" ltac_term:(G)) | idtac "SSR	conv.1g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "conv.1g" "56" ltac_term:(G)) | idtac "SSR	conv.1g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "conv.1g" "57" ltac_term:(G)) | idtac "SSR	conv.1g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "conv.1g" "58" ltac_term:(G)) | idtac "SSR	conv.1g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "conv.1g" "59" ltac_term:(G)) | idtac "SSR	conv.1g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = _); elpi z_report "conv.1g" "60" ltac_term:(G)) | idtac "SSR	conv.1g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X); elpi z_report "conv.1g" "61" ltac_term:(G)) | idtac "SSR	conv.1g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X * _); elpi z_report "conv.1g" "62" ltac_term:(G)) | idtac "SSR	conv.1g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X * _); elpi z_report "conv.1g" "63" ltac_term:(G)) | idtac "SSR	conv.1g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X * _); elpi z_report "conv.1g" "64" ltac_term:(G)) | idtac "SSR	conv.1g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X = _); elpi z_report "conv.1g" "65" ltac_term:(G)) | idtac "SSR	conv.1g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X * _); elpi z_report "conv.1g" "66" ltac_term:(G)) | idtac "SSR	conv.1g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = _ /\ _); elpi z_report "conv.1g" "67" ltac_term:(G)) | idtac "SSR	conv.1g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X * _); elpi z_report "conv.1g" "68" ltac_term:(G)) | idtac "SSR	conv.1g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + S X * _); elpi z_report "conv.1g" "69" ltac_term:(G)) | idtac "SSR	conv.1g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X * _ = _); elpi z_report "conv.1g" "70" ltac_term:(G)) | idtac "SSR	conv.1g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + S X * _ = _); elpi z_report "conv.1g" "71" ltac_term:(G)) | idtac "SSR	conv.1g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X * _ = _ /\ _); elpi z_report "conv.1g" "72" ltac_term:(G)) | idtac "SSR	conv.1g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + S X * _ = _ /\ _); elpi z_report "conv.1g" "73" ltac_term:(G)) | idtac "SSR	conv.1g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "conv.1g" "74" ltac_term:(G)) | idtac "SSR	conv.1g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "conv.1g" "75" ltac_term:(G)) | idtac "SSR	conv.1g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "conv.1g" "76" ltac_term:(G)) | idtac "SSR	conv.1g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "conv.1g" "77" ltac_term:(G)) | idtac "SSR	conv.1g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "conv.1g" "78" ltac_term:(G)) | idtac "SSR	conv.1g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) * _); elpi z_report "conv.1g" "79" ltac_term:(G)) | idtac "SSR	conv.1g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S (S X) * _); elpi z_report "conv.1g" "80" ltac_term:(G)) | idtac "SSR	conv.1g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S (S X) * _ = _); elpi z_report "conv.1g" "81" ltac_term:(G)) | idtac "SSR	conv.1g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S (S X) * _ = _ /\ _); elpi z_report "conv.1g" "82" ltac_term:(G)) | idtac "SSR	conv.1g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "conv.1g" "83" ltac_term:(G)) | idtac "SSR	conv.1g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "conv.1g" "84" ltac_term:(G)) | idtac "SSR	conv.1g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "conv.1g" "85" ltac_term:(G)) | idtac "SSR	conv.1g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X); elpi z_report "conv.1g" "86" ltac_term:(G)) | idtac "SSR	conv.1g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X = _); elpi z_report "conv.1g" "87" ltac_term:(G)) | idtac "SSR	conv.1g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X = _ /\ _); elpi z_report "conv.1g" "88" ltac_term:(G)) | idtac "SSR	conv.1g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "conv.1g" "89" ltac_term:(G)) | idtac "SSR	conv.1g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "conv.1g" "90" ltac_term:(G)) | idtac "SSR	conv.1g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "conv.1g" "91" ltac_term:(G)) | idtac "SSR	conv.1g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (m + _); elpi z_report "conv.1g" "92" ltac_term:(G)) | idtac "SSR	conv.1g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "conv.1g" "93" ltac_term:(G)) | idtac "SSR	conv.1g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "conv.1g" "94" ltac_term:(G)) | idtac "SSR	conv.1g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (m + _ in X in X /\ _); elpi z_report "conv.1g" "95" ltac_term:(G)) | idtac "SSR	conv.1g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X /\ _); elpi z_report "conv.1g" "96" ltac_term:(G)) | idtac "SSR	conv.1g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m + (m + n)); elpi z_report "conv.1g" "97" ltac_term:(G)) | idtac "SSR	conv.1g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "conv.1g" "98" ltac_term:(G)) | idtac "SSR	conv.1g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "conv.1g" "99" ltac_term:(G)) | idtac "SSR	conv.1g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "conv.1g" "100" ltac_term:(G)) | idtac "SSR	conv.1g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ /\ _); elpi z_report "conv.1g" "101" ltac_term:(G)) | idtac "SSR	conv.1g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (m + n)); elpi z_report "conv.1g" "102" ltac_term:(G)) | idtac "SSR	conv.1g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "conv.1g" "103" ltac_term:(G)) | idtac "SSR	conv.1g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "conv.1g" "104" ltac_term:(G)) | idtac "SSR	conv.1g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n); elpi z_report "conv.1g" "105" ltac_term:(G)) | idtac "SSR	conv.1g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in m + X); elpi z_report "conv.1g" "106" ltac_term:(G)) | idtac "SSR	conv.1g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "conv.1g" "107" ltac_term:(G)) | idtac "SSR	conv.1g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "conv.1g" "108" ltac_term:(G)) | idtac "SSR	conv.1g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n in X in _ = X); elpi z_report "conv.1g" "109" ltac_term:(G)) | idtac "SSR	conv.1g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n in X in X /\ _); elpi z_report "conv.1g" "110" ltac_term:(G)) | idtac "SSR	conv.1g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = _ + X); elpi z_report "conv.1g" "111" ltac_term:(G)) | idtac "SSR	conv.1g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X /\ _); elpi z_report "conv.1g" "112" ltac_term:(G)) | idtac "SSR	conv.1g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n in X in _ = X /\ _); elpi z_report "conv.1g" "113" ltac_term:(G)) | idtac "SSR	conv.1g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = _ + X /\ _); elpi z_report "conv.1g" "114" ltac_term:(G)) | idtac "SSR	conv.1g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m + n); elpi z_report "conv.1g" "115" ltac_term:(G)) | idtac "SSR	conv.1g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "conv.1g" "116" ltac_term:(G)) | idtac "SSR	conv.1g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "conv.1g" "117" ltac_term:(G)) | idtac "SSR	conv.1g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + n); elpi z_report "conv.1g" "118" ltac_term:(G)) | idtac "SSR	conv.1g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "conv.1g" "119" ltac_term:(G)) | idtac "SSR	conv.1g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (X + _)); elpi z_report "conv.1g" "120" ltac_term:(G)) | idtac "SSR	conv.1g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (X + _) /\ _); elpi z_report "conv.1g" "121" ltac_term:(G)) | idtac "SSR	conv.1g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (m); elpi z_report "conv.1g" "122" ltac_term:(G)) | idtac "SSR	conv.1g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "conv.1g" "123" ltac_term:(G)) | idtac "SSR	conv.1g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "conv.1g" "124" ltac_term:(G)) | idtac "SSR	conv.1g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "conv.1g" "125" ltac_term:(G)) | idtac "SSR	conv.1g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ + X)); elpi z_report "conv.1g" "126" ltac_term:(G)) | idtac "SSR	conv.1g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ + X) /\ _); elpi z_report "conv.1g" "127" ltac_term:(G)) | idtac "SSR	conv.1g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "conv.1g" "128" ltac_term:(G)) | idtac "SSR	conv.1g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "conv.1g" "129" ltac_term:(G)) | idtac "SSR	conv.1g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "conv.1g" "130" ltac_term:(G)) | idtac "SSR	conv.1g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = n); elpi z_report "conv.1g" "131" ltac_term:(G)) | idtac "SSR	conv.1g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "conv.1g" "132" ltac_term:(G)) | idtac "SSR	conv.1g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 + n = n); elpi z_report "conv.1g" "133" ltac_term:(G)) | idtac "SSR	conv.1g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "conv.1g" "134" ltac_term:(G)) | idtac "SSR	conv.1g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "conv.1g" "135" ltac_term:(G)) | idtac "SSR	conv.1g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "conv.1g" "136" ltac_term:(G)) | idtac "SSR	conv.1g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "conv.1g" "137" ltac_term:(G)) | idtac "SSR	conv.1g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "conv.1g" "138" ltac_term:(G)) | idtac "SSR	conv.1g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "conv.1g" "139" ltac_term:(G)) | idtac "SSR	conv.1g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _); elpi z_report "conv.1g" "140" ltac_term:(G)) | idtac "SSR	conv.1g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = n); elpi z_report "conv.1g" "141" ltac_term:(G)) | idtac "SSR	conv.1g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ X); elpi z_report "conv.1g" "142" ltac_term:(G)) | idtac "SSR	conv.1g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "conv.1g" "143" ltac_term:(G)) | idtac "SSR	conv.1g	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _ as X in X = _); elpi z_report "conv.1g" "144" ltac_term:(G)) | idtac "SSR	conv.1g	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ /\ X = _); elpi z_report "conv.1g" "145" ltac_term:(G)) | idtac "SSR	conv.1g	145	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 + n); elpi z_report "conv.1g" "146" ltac_term:(G)) | idtac "SSR	conv.1g	146	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "conv.1g" "147" ltac_term:(G)) | idtac "SSR	conv.1g	147	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "conv.1g" "148" ltac_term:(G)) | idtac "SSR	conv.1g	148	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "conv.1g" "149" ltac_term:(G)) | idtac "SSR	conv.1g	149	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + n = _); elpi z_report "conv.1g" "150" ltac_term:(G)) | idtac "SSR	conv.1g	150	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X + _ = _); elpi z_report "conv.1g" "151" ltac_term:(G)) | idtac "SSR	conv.1g	151	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "conv.1g" "152" ltac_term:(G)) | idtac "SSR	conv.1g	152	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "conv.1g" "153" ltac_term:(G)) | idtac "SSR	conv.1g	153	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "conv.1g" "154" ltac_term:(G)) | idtac "SSR	conv.1g	154	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + X); elpi z_report "conv.1g" "155" ltac_term:(G)) | idtac "SSR	conv.1g	155	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + X = _); elpi z_report "conv.1g" "156" ltac_term:(G)) | idtac "SSR	conv.1g	156	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ + X = _); elpi z_report "conv.1g" "157" ltac_term:(G)) | idtac "SSR	conv.1g	157	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "conv.1g" "158" ltac_term:(G)) | idtac "SSR	conv.1g	158	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "conv.1g" "159" ltac_term:(G)) | idtac "SSR	conv.1g	159	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "conv.1g" "160" ltac_term:(G)) | idtac "SSR	conv.1g	160	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + _ = X); elpi z_report "conv.1g" "161" ltac_term:(G)) | idtac "SSR	conv.1g	161	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "conv.1g" "162" ltac_term:(G)) | idtac "SSR	conv.1g	162	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "conv.1g" "163" ltac_term:(G)) | idtac "SSR	conv.1g	163	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "conv.1g" "164" ltac_term:(G)) | idtac "SSR	conv.1g	164	error" ].
Abort.

(* implicit and hidden arguments, casts *)
Goal forall (a : nat) (l : list nat), length (a :: l) = S (length l) /\ (a : nat) = a.
intros a l.
change (length (a :: l) = S (length l) /\ (a : nat) = a).
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "hidden.1" "1" ltac_term:(G)) | idtac "SSR	hidden.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _); elpi z_report "hidden.1" "2" ltac_term:(G)) | idtac "SSR	hidden.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "hidden.1" "3" ltac_term:(G)) | idtac "SSR	hidden.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "hidden.1" "4" ltac_term:(G)) | idtac "SSR	hidden.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (list nat); elpi z_report "hidden.1" "5" ltac_term:(G)) | idtac "SSR	hidden.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@length nat _); elpi z_report "hidden.1" "6" ltac_term:(G)) | idtac "SSR	hidden.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X); elpi z_report "hidden.1" "7" ltac_term:(G)) | idtac "SSR	hidden.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "hidden.1" "8" ltac_term:(G)) | idtac "SSR	hidden.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "hidden.1" "9" ltac_term:(G)) | idtac "SSR	hidden.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "hidden.1" "10" ltac_term:(G)) | idtac "SSR	hidden.1	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "hidden.1" "11" ltac_term:(G)) | idtac "SSR	hidden.1	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "hidden.1" "12" ltac_term:(G)) | idtac "SSR	hidden.1	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "hidden.1g" "1" ltac_term:(G)) | idtac "SSR	hidden.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length (a :: l) = S (length l) /\ (a : nat) = a); elpi z_report "hidden.1g" "2" ltac_term:(G)) | idtac "SSR	hidden.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "hidden.1g" "3" ltac_term:(G)) | idtac "SSR	hidden.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "hidden.1g" "4" ltac_term:(G)) | idtac "SSR	hidden.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "hidden.1g" "5" ltac_term:(G)) | idtac "SSR	hidden.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "hidden.1g" "6" ltac_term:(G)) | idtac "SSR	hidden.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "hidden.1g" "7" ltac_term:(G)) | idtac "SSR	hidden.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length (a :: l) = S (length l)); elpi z_report "hidden.1g" "8" ltac_term:(G)) | idtac "SSR	hidden.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "hidden.1g" "9" ltac_term:(G)) | idtac "SSR	hidden.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "hidden.1g" "10" ltac_term:(G)) | idtac "SSR	hidden.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "hidden.1g" "11" ltac_term:(G)) | idtac "SSR	hidden.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "hidden.1g" "12" ltac_term:(G)) | idtac "SSR	hidden.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _); elpi z_report "hidden.1g" "13" ltac_term:(G)) | idtac "SSR	hidden.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "hidden.1g" "14" ltac_term:(G)) | idtac "SSR	hidden.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in X = _); elpi z_report "hidden.1g" "15" ltac_term:(G)) | idtac "SSR	hidden.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in X /\ _); elpi z_report "hidden.1g" "16" ltac_term:(G)) | idtac "SSR	hidden.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "hidden.1g" "17" ltac_term:(G)) | idtac "SSR	hidden.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in X = _ /\ _); elpi z_report "hidden.1g" "18" ltac_term:(G)) | idtac "SSR	hidden.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length (a :: l)); elpi z_report "hidden.1g" "19" ltac_term:(G)) | idtac "SSR	hidden.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length); elpi z_report "hidden.1g" "20" ltac_term:(G)) | idtac "SSR	hidden.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length); elpi z_report "hidden.1g" "21" ltac_term:(G)) | idtac "SSR	hidden.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "hidden.1g" "22" ltac_term:(G)) | idtac "SSR	hidden.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "hidden.1g" "23" ltac_term:(G)) | idtac "SSR	hidden.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _); elpi z_report "hidden.1g" "24" ltac_term:(G)) | idtac "SSR	hidden.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X); elpi z_report "hidden.1g" "25" ltac_term:(G)) | idtac "SSR	hidden.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in X = _); elpi z_report "hidden.1g" "26" ltac_term:(G)) | idtac "SSR	hidden.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in X /\ _); elpi z_report "hidden.1g" "27" ltac_term:(G)) | idtac "SSR	hidden.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ as X in length X); elpi z_report "hidden.1g" "28" ltac_term:(G)) | idtac "SSR	hidden.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X = _); elpi z_report "hidden.1g" "29" ltac_term:(G)) | idtac "SSR	hidden.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ in X in X = _ /\ _); elpi z_report "hidden.1g" "30" ltac_term:(G)) | idtac "SSR	hidden.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ as X in length X = _); elpi z_report "hidden.1g" "31" ltac_term:(G)) | idtac "SSR	hidden.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length X = _ /\ _); elpi z_report "hidden.1g" "32" ltac_term:(G)) | idtac "SSR	hidden.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ :: _ as X in length X = _ /\ _); elpi z_report "hidden.1g" "33" ltac_term:(G)) | idtac "SSR	hidden.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a :: l); elpi z_report "hidden.1g" "34" ltac_term:(G)) | idtac "SSR	hidden.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@cons); elpi z_report "hidden.1g" "35" ltac_term:(G)) | idtac "SSR	hidden.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@cons); elpi z_report "hidden.1g" "36" ltac_term:(G)) | idtac "SSR	hidden.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "hidden.1g" "37" ltac_term:(G)) | idtac "SSR	hidden.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "hidden.1g" "38" ltac_term:(G)) | idtac "SSR	hidden.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X :: _); elpi z_report "hidden.1g" "39" ltac_term:(G)) | idtac "SSR	hidden.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (X :: _)); elpi z_report "hidden.1g" "40" ltac_term:(G)) | idtac "SSR	hidden.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (X :: _) = _); elpi z_report "hidden.1g" "41" ltac_term:(G)) | idtac "SSR	hidden.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (X :: _) = _ /\ _); elpi z_report "hidden.1g" "42" ltac_term:(G)) | idtac "SSR	hidden.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "hidden.1g" "43" ltac_term:(G)) | idtac "SSR	hidden.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "hidden.1g" "44" ltac_term:(G)) | idtac "SSR	hidden.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ :: X); elpi z_report "hidden.1g" "45" ltac_term:(G)) | idtac "SSR	hidden.1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (_ :: X)); elpi z_report "hidden.1g" "46" ltac_term:(G)) | idtac "SSR	hidden.1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (_ :: X) = _); elpi z_report "hidden.1g" "47" ltac_term:(G)) | idtac "SSR	hidden.1g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in length (_ :: X) = _ /\ _); elpi z_report "hidden.1g" "48" ltac_term:(G)) | idtac "SSR	hidden.1g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(l); elpi z_report "hidden.1g" "49" ltac_term:(G)) | idtac "SSR	hidden.1g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(l); elpi z_report "hidden.1g" "50" ltac_term:(G)) | idtac "SSR	hidden.1g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "hidden.1g" "51" ltac_term:(G)) | idtac "SSR	hidden.1g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "hidden.1g" "52" ltac_term:(G)) | idtac "SSR	hidden.1g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X); elpi z_report "hidden.1g" "53" ltac_term:(G)) | idtac "SSR	hidden.1g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X /\ _); elpi z_report "hidden.1g" "54" ltac_term:(G)) | idtac "SSR	hidden.1g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "hidden.1g" "55" ltac_term:(G)) | idtac "SSR	hidden.1g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X /\ _); elpi z_report "hidden.1g" "56" ltac_term:(G)) | idtac "SSR	hidden.1g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S (length l)); elpi z_report "hidden.1g" "57" ltac_term:(G)) | idtac "SSR	hidden.1g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "hidden.1g" "58" ltac_term:(G)) | idtac "SSR	hidden.1g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "hidden.1g" "59" ltac_term:(G)) | idtac "SSR	hidden.1g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "hidden.1g" "60" ltac_term:(G)) | idtac "SSR	hidden.1g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l); elpi z_report "hidden.1g" "61" ltac_term:(G)) | idtac "SSR	hidden.1g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in S X); elpi z_report "hidden.1g" "62" ltac_term:(G)) | idtac "SSR	hidden.1g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X); elpi z_report "hidden.1g" "63" ltac_term:(G)) | idtac "SSR	hidden.1g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X); elpi z_report "hidden.1g" "64" ltac_term:(G)) | idtac "SSR	hidden.1g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length l in X in X /\ _); elpi z_report "hidden.1g" "65" ltac_term:(G)) | idtac "SSR	hidden.1g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in _ = S X); elpi z_report "hidden.1g" "66" ltac_term:(G)) | idtac "SSR	hidden.1g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ in X in _ = X /\ _); elpi z_report "hidden.1g" "67" ltac_term:(G)) | idtac "SSR	hidden.1g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X /\ _); elpi z_report "hidden.1g" "68" ltac_term:(G)) | idtac "SSR	hidden.1g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length _ as X in _ = S X /\ _); elpi z_report "hidden.1g" "69" ltac_term:(G)) | idtac "SSR	hidden.1g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(length l); elpi z_report "hidden.1g" "70" ltac_term:(G)) | idtac "SSR	hidden.1g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (length); elpi z_report "hidden.1g" "71" ltac_term:(G)) | idtac "SSR	hidden.1g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length); elpi z_report "hidden.1g" "72" ltac_term:(G)) | idtac "SSR	hidden.1g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(length); elpi z_report "hidden.1g" "73" ltac_term:(G)) | idtac "SSR	hidden.1g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "hidden.1g" "74" ltac_term:(G)) | idtac "SSR	hidden.1g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "hidden.1g" "75" ltac_term:(G)) | idtac "SSR	hidden.1g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (length X)); elpi z_report "hidden.1g" "76" ltac_term:(G)) | idtac "SSR	hidden.1g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S (length X)); elpi z_report "hidden.1g" "77" ltac_term:(G)) | idtac "SSR	hidden.1g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S (length X) /\ _); elpi z_report "hidden.1g" "78" ltac_term:(G)) | idtac "SSR	hidden.1g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (l); elpi z_report "hidden.1g" "79" ltac_term:(G)) | idtac "SSR	hidden.1g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l); elpi z_report "hidden.1g" "80" ltac_term:(G)) | idtac "SSR	hidden.1g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(l); elpi z_report "hidden.1g" "81" ltac_term:(G)) | idtac "SSR	hidden.1g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "hidden.1g" "82" ltac_term:(G)) | idtac "SSR	hidden.1g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "hidden.1g" "83" ltac_term:(G)) | idtac "SSR	hidden.1g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((a : nat) = _); elpi z_report "hidden.1g" "84" ltac_term:(G)) | idtac "SSR	hidden.1g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((a : nat) = a); elpi z_report "hidden.1g" "85" ltac_term:(G)) | idtac "SSR	hidden.1g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "hidden.1g" "86" ltac_term:(G)) | idtac "SSR	hidden.1g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "hidden.1g" "87" ltac_term:(G)) | idtac "SSR	hidden.1g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "hidden.1g" "88" ltac_term:(G)) | idtac "SSR	hidden.1g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "hidden.1g" "89" ltac_term:(G)) | idtac "SSR	hidden.1g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(nat); elpi z_report "hidden.1g" "90" ltac_term:(G)) | idtac "SSR	hidden.1g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(nat); elpi z_report "hidden.1g" "91" ltac_term:(G)) | idtac "SSR	hidden.1g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "hidden.1g" "92" ltac_term:(G)) | idtac "SSR	hidden.1g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "hidden.1g" "93" ltac_term:(G)) | idtac "SSR	hidden.1g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "hidden.1g" "94" ltac_term:(G)) | idtac "SSR	hidden.1g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (a : nat) = X); elpi z_report "hidden.1g" "95" ltac_term:(G)) | idtac "SSR	hidden.1g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "hidden.1g" "96" ltac_term:(G)) | idtac "SSR	hidden.1g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "hidden.1g" "97" ltac_term:(G)) | idtac "SSR	hidden.1g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "hidden.1g" "98" ltac_term:(G)) | idtac "SSR	hidden.1g	98	error" ].
Abort.

(* binders: patterns under forall and fun, bound variables in the redex *)
Goal forall a : nat, (forall n : nat, n + a = a + n) /\ (fun k : nat => k + 0) a = a.
intros a.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + a); elpi z_report "binders.1" "1" ltac_term:(G)) | idtac "SSR	binders.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "binders.1" "2" ltac_term:(G)) | idtac "SSR	binders.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + 0); elpi z_report "binders.1" "3" ltac_term:(G)) | idtac "SSR	binders.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "binders.1" "4" ltac_term:(G)) | idtac "SSR	binders.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (forall n, _); elpi z_report "binders.1" "5" ltac_term:(G)) | idtac "SSR	binders.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (fun k : nat => _); elpi z_report "binders.1" "6" ltac_term:(G)) | idtac "SSR	binders.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (fun k : nat => _) X = _); elpi z_report "binders.1" "7" ltac_term:(G)) | idtac "SSR	binders.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "binders.1" "8" ltac_term:(G)) | idtac "SSR	binders.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ = _); elpi z_report "binders.1" "9" ltac_term:(G)) | idtac "SSR	binders.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "binders.1" "10" ltac_term:(G)) | idtac "SSR	binders.1	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "binders.1g" "1" ltac_term:(G)) | idtac "SSR	binders.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "binders.1g" "2" ltac_term:(G)) | idtac "SSR	binders.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "binders.1g" "3" ltac_term:(G)) | idtac "SSR	binders.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "binders.1g" "4" ltac_term:(G)) | idtac "SSR	binders.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (forall n : nat, n + a = a + n); elpi z_report "binders.1g" "5" ltac_term:(G)) | idtac "SSR	binders.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(forall n : nat, n + a = a + n); elpi z_report "binders.1g" "6" ltac_term:(G)) | idtac "SSR	binders.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "binders.1g" "7" ltac_term:(G)) | idtac "SSR	binders.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "binders.1g" "8" ltac_term:(G)) | idtac "SSR	binders.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "binders.1g" "9" ltac_term:(G)) | idtac "SSR	binders.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "binders.1g" "10" ltac_term:(G)) | idtac "SSR	binders.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "binders.1g" "11" ltac_term:(G)) | idtac "SSR	binders.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "binders.1g" "12" ltac_term:(G)) | idtac "SSR	binders.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "binders.1g" "13" ltac_term:(G)) | idtac "SSR	binders.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "binders.1g" "14" ltac_term:(G)) | idtac "SSR	binders.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "binders.1g" "15" ltac_term:(G)) | idtac "SSR	binders.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "binders.1g" "16" ltac_term:(G)) | idtac "SSR	binders.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "binders.1g" "17" ltac_term:(G)) | idtac "SSR	binders.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "binders.1g" "18" ltac_term:(G)) | idtac "SSR	binders.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "binders.1g" "19" ltac_term:(G)) | idtac "SSR	binders.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "binders.1g" "20" ltac_term:(G)) | idtac "SSR	binders.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "binders.1g" "21" ltac_term:(G)) | idtac "SSR	binders.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "binders.1g" "22" ltac_term:(G)) | idtac "SSR	binders.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "binders.1g" "23" ltac_term:(G)) | idtac "SSR	binders.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "binders.1g" "24" ltac_term:(G)) | idtac "SSR	binders.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "binders.1g" "25" ltac_term:(G)) | idtac "SSR	binders.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "binders.1g" "26" ltac_term:(G)) | idtac "SSR	binders.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "binders.1g" "27" ltac_term:(G)) | idtac "SSR	binders.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "binders.1g" "28" ltac_term:(G)) | idtac "SSR	binders.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "binders.1g" "29" ltac_term:(G)) | idtac "SSR	binders.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "binders.1g" "30" ltac_term:(G)) | idtac "SSR	binders.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "binders.1g" "31" ltac_term:(G)) | idtac "SSR	binders.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "binders.1g" "32" ltac_term:(G)) | idtac "SSR	binders.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "binders.1g" "33" ltac_term:(G)) | idtac "SSR	binders.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "binders.1g" "34" ltac_term:(G)) | idtac "SSR	binders.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "binders.1g" "35" ltac_term:(G)) | idtac "SSR	binders.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "binders.1g" "36" ltac_term:(G)) | idtac "SSR	binders.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "binders.1g" "37" ltac_term:(G)) | idtac "SSR	binders.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "binders.1g" "38" ltac_term:(G)) | idtac "SSR	binders.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "binders.1g" "39" ltac_term:(G)) | idtac "SSR	binders.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "binders.1g" "40" ltac_term:(G)) | idtac "SSR	binders.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "binders.1g" "41" ltac_term:(G)) | idtac "SSR	binders.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "binders.1g" "42" ltac_term:(G)) | idtac "SSR	binders.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "binders.1g" "43" ltac_term:(G)) | idtac "SSR	binders.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "binders.1g" "44" ltac_term:(G)) | idtac "SSR	binders.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "binders.1g" "45" ltac_term:(G)) | idtac "SSR	binders.1g	45	error" ].
Abort.

Goal forall a : nat, (forall n : nat, n + 0 = n) -> a + 0 = a.
intros a H.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + 0); elpi z_report "binders.2" "1" ltac_term:(G)) | idtac "SSR	binders.2	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "binders.2" "2" ltac_term:(G)) | idtac "SSR	binders.2	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "binders.2" "3" ltac_term:(G)) | idtac "SSR	binders.2	3	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + 0) in H; elpi z_report "hyp.1" "1" ltac_term:(G) "H") | idtac "SSR	hyp.1	1	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ = _) in H; elpi z_report "hyp.1" "2" ltac_term:(G) "H") | idtac "SSR	hyp.1	2	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = X) in H; elpi z_report "hyp.1" "3" ltac_term:(G) "H") | idtac "SSR	hyp.1	3	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (nat) in H; elpi z_report "hyp.1" "4" ltac_term:(G) "H") | idtac "SSR	hyp.1	4	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (forall n, _) in H; elpi z_report "hyp.1" "5" ltac_term:(G) "H") | idtac "SSR	hyp.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "binders.2g" "1" ltac_term:(G)) | idtac "SSR	binders.2g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + 0 = a); elpi z_report "binders.2g" "2" ltac_term:(G)) | idtac "SSR	binders.2g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "binders.2g" "3" ltac_term:(G)) | idtac "SSR	binders.2g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "binders.2g" "4" ltac_term:(G)) | idtac "SSR	binders.2g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "binders.2g" "5" ltac_term:(G)) | idtac "SSR	binders.2g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "binders.2g" "6" ltac_term:(G)) | idtac "SSR	binders.2g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "binders.2g" "7" ltac_term:(G)) | idtac "SSR	binders.2g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "binders.2g" "8" ltac_term:(G)) | idtac "SSR	binders.2g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "binders.2g" "9" ltac_term:(G)) | idtac "SSR	binders.2g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + 0); elpi z_report "binders.2g" "10" ltac_term:(G)) | idtac "SSR	binders.2g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "binders.2g" "11" ltac_term:(G)) | idtac "SSR	binders.2g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "binders.2g" "12" ltac_term:(G)) | idtac "SSR	binders.2g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "binders.2g" "13" ltac_term:(G)) | idtac "SSR	binders.2g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "binders.2g" "14" ltac_term:(G)) | idtac "SSR	binders.2g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "binders.2g" "15" ltac_term:(G)) | idtac "SSR	binders.2g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "binders.2g" "16" ltac_term:(G)) | idtac "SSR	binders.2g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "binders.2g" "17" ltac_term:(G)) | idtac "SSR	binders.2g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "binders.2g" "18" ltac_term:(G)) | idtac "SSR	binders.2g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "binders.2g" "19" ltac_term:(G)) | idtac "SSR	binders.2g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "binders.2g" "20" ltac_term:(G)) | idtac "SSR	binders.2g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "binders.2g" "21" ltac_term:(G)) | idtac "SSR	binders.2g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "binders.2g" "22" ltac_term:(G)) | idtac "SSR	binders.2g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "binders.2g" "23" ltac_term:(G)) | idtac "SSR	binders.2g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "binders.2g" "24" ltac_term:(G)) | idtac "SSR	binders.2g	24	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (forall n : nat, n + 0 = n) in H; elpi z_report "binders.2g" "25" ltac_term:(G) "H") | idtac "SSR	binders.2g	25	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(forall n : nat, n + 0 = n) in H; elpi z_report "binders.2g" "26" ltac_term:(G) "H") | idtac "SSR	binders.2g	26	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H; elpi z_report "binders.2g" "27" ltac_term:(G) "H") | idtac "SSR	binders.2g	27	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H; elpi z_report "binders.2g" "28" ltac_term:(G) "H") | idtac "SSR	binders.2g	28	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (@eq) in H; elpi z_report "binders.2g" "29" ltac_term:(G) "H") | idtac "SSR	binders.2g	29	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H; elpi z_report "binders.2g" "30" ltac_term:(G) "H") | idtac "SSR	binders.2g	30	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (nat) in H; elpi z_report "binders.2g" "31" ltac_term:(G) "H") | idtac "SSR	binders.2g	31	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H; elpi z_report "binders.2g" "32" ltac_term:(G) "H") | idtac "SSR	binders.2g	32	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H; elpi z_report "binders.2g" "33" ltac_term:(G) "H") | idtac "SSR	binders.2g	33	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (Nat.add) in H; elpi z_report "binders.2g" "34" ltac_term:(G) "H") | idtac "SSR	binders.2g	34	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H; elpi z_report "binders.2g" "35" ltac_term:(G) "H") | idtac "SSR	binders.2g	35	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (0) in H; elpi z_report "binders.2g" "36" ltac_term:(G) "H") | idtac "SSR	binders.2g	36	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(0) in H; elpi z_report "binders.2g" "37" ltac_term:(G) "H") | idtac "SSR	binders.2g	37	error" ].
Abort.

(* hypotheses *)
Goal forall (f : nat -> nat) a b, f a + f b = f (a + b) -> f (a + b) = f a + f b -> True.
intros f a b H1 H2.
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _) in H1; elpi z_report "hyp.2" "1" ltac_term:(G) "H1") | idtac "SSR	hyp.2	1	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ = f X) in H1; elpi z_report "hyp.2" "2" ltac_term:(G) "H1") | idtac "SSR	hyp.2	2	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _ in X in _ = X) in H1; elpi z_report "hyp.2" "3" ltac_term:(G) "H1") | idtac "SSR	hyp.2	3	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(f _) in H1; elpi z_report "hyp.2" "4" ltac_term:(G) "H1") | idtac "SSR	hyp.2	4	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f a + _) in H1; elpi z_report "hyp.2" "5" ltac_term:(G) "H1") | idtac "SSR	hyp.2	5	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X) in H1; elpi z_report "hyp.2" "6" ltac_term:(G) "H1") | idtac "SSR	hyp.2	6	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (a + _) in H1; elpi z_report "hyp.2" "7" ltac_term:(G) "H1") | idtac "SSR	hyp.2	7	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _) in H2; elpi z_report "hyp.3" "1" ltac_term:(G) "H2") | idtac "SSR	hyp.3	1	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in X = _) in H2; elpi z_report "hyp.3" "2" ltac_term:(G) "H2") | idtac "SSR	hyp.3	2	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (_ + _) in H2; elpi z_report "hyp.3" "3" ltac_term:(G) "H2") | idtac "SSR	hyp.3	3	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {3}(f _) in H2; elpi z_report "hyp.3" "4" ltac_term:(G) "H2") | idtac "SSR	hyp.3	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (True); elpi z_report "hyp.2g" "1" ltac_term:(G)) | idtac "SSR	hyp.2g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(True); elpi z_report "hyp.2g" "2" ltac_term:(G)) | idtac "SSR	hyp.2g	2	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (_ = _) in H2; elpi z_report "hyp.2g" "3" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	3	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(f (a + b) = f a + f b) in H2; elpi z_report "hyp.2g" "4" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	4	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (@eq) in H2; elpi z_report "hyp.2g" "5" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	5	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H2; elpi z_report "hyp.2g" "6" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	6	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (nat) in H2; elpi z_report "hyp.2g" "7" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	7	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H2; elpi z_report "hyp.2g" "8" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	8	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _) in H2; elpi z_report "hyp.2g" "9" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	9	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in X = _) in H2; elpi z_report "hyp.2g" "10" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	10	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _ as X in X = _) in H2; elpi z_report "hyp.2g" "11" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	11	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(f (a + b)) in H2; elpi z_report "hyp.2g" "12" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	12	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(f) in H2; elpi z_report "hyp.2g" "13" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	13	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(f) in H2; elpi z_report "hyp.2g" "14" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	14	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (_ + _) in H2; elpi z_report "hyp.2g" "15" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	15	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f X) in H2; elpi z_report "hyp.2g" "16" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	16	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X) in H2; elpi z_report "hyp.2g" "17" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	17	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X = _) in H2; elpi z_report "hyp.2g" "18" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	18	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f X = _) in H2; elpi z_report "hyp.2g" "19" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	19	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X = _) in H2; elpi z_report "hyp.2g" "20" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	20	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(a + b) in H2; elpi z_report "hyp.2g" "21" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	21	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H2; elpi z_report "hyp.2g" "22" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	22	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H2; elpi z_report "hyp.2g" "23" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	23	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in X + _) in H2; elpi z_report "hyp.2g" "24" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	24	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f (X + _)) in H2; elpi z_report "hyp.2g" "25" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	25	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f (X + _) = _) in H2; elpi z_report "hyp.2g" "26" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	26	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(a) in H2; elpi z_report "hyp.2g" "27" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	27	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(a) in H2; elpi z_report "hyp.2g" "28" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	28	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in _ + X) in H2; elpi z_report "hyp.2g" "29" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	29	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X)) in H2; elpi z_report "hyp.2g" "30" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	30	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X) = _) in H2; elpi z_report "hyp.2g" "31" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	31	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(b) in H2; elpi z_report "hyp.2g" "32" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	32	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(b) in H2; elpi z_report "hyp.2g" "33" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	33	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in _ = X) in H2; elpi z_report "hyp.2g" "34" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	34	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X) in H2; elpi z_report "hyp.2g" "35" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	35	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f a + _) in H2; elpi z_report "hyp.2g" "36" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	36	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(f a + f b) in H2; elpi z_report "hyp.2g" "37" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	37	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (Nat.add) in H2; elpi z_report "hyp.2g" "38" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	38	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add) in H2; elpi z_report "hyp.2g" "39" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	39	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add) in H2; elpi z_report "hyp.2g" "40" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	40	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f a) in H2; elpi z_report "hyp.2g" "41" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	41	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _ as X in X + _) in H2; elpi z_report "hyp.2g" "42" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	42	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _ in X in _ = X) in H2; elpi z_report "hyp.2g" "43" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	43	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _) in H2; elpi z_report "hyp.2g" "44" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	44	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in X + f b) in H2; elpi z_report "hyp.2g" "45" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	45	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ = X + _) in H2; elpi z_report "hyp.2g" "46" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	46	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(f a) in H2; elpi z_report "hyp.2g" "47" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	47	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(f) in H2; elpi z_report "hyp.2g" "48" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	48	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(f) in H2; elpi z_report "hyp.2g" "49" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	49	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f X + _) in H2; elpi z_report "hyp.2g" "50" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	50	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in _ = f X + _) in H2; elpi z_report "hyp.2g" "51" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	51	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (a) in H2; elpi z_report "hyp.2g" "52" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	52	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(a) in H2; elpi z_report "hyp.2g" "53" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	53	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(a) in H2; elpi z_report "hyp.2g" "54" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	54	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f b) in H2; elpi z_report "hyp.2g" "55" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	55	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ + X) in H2; elpi z_report "hyp.2g" "56" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	56	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X) in H2; elpi z_report "hyp.2g" "57" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	57	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in f a + X) in H2; elpi z_report "hyp.2g" "58" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	58	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f b in X in _ = X) in H2; elpi z_report "hyp.2g" "59" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	59	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ = _ + X) in H2; elpi z_report "hyp.2g" "60" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	60	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {1}(f b) in H2; elpi z_report "hyp.2g" "61" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	61	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (f) in H2; elpi z_report "hyp.2g" "62" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	62	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {3}(f) in H2; elpi z_report "hyp.2g" "63" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	63	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {3}(f) in H2; elpi z_report "hyp.2g" "64" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	64	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in _ + f X) in H2; elpi z_report "hyp.2g" "65" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	65	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + f X) in H2; elpi z_report "hyp.2g" "66" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	66	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := (b) in H2; elpi z_report "hyp.2g" "67" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	67	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(b) in H2; elpi z_report "hyp.2g" "68" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	68	error" ].
let G := type of H2 in first [ assert_succeeds (set pattern_select_z := {2}(b) in H2; elpi z_report "hyp.2g" "69" ltac_term:(G) "H2") | idtac "SSR	hyp.2g	69	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (_ = _) in H1; elpi z_report "hyp.2g" "70" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	70	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(f a + f b = f (a + b)) in H1; elpi z_report "hyp.2g" "71" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	71	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (@eq) in H1; elpi z_report "hyp.2g" "72" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	72	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H1; elpi z_report "hyp.2g" "73" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	73	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (nat) in H1; elpi z_report "hyp.2g" "74" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	74	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H1; elpi z_report "hyp.2g" "75" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	75	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (_ + _) in H1; elpi z_report "hyp.2g" "76" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	76	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in X = _) in H1; elpi z_report "hyp.2g" "77" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	77	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _) in H1; elpi z_report "hyp.2g" "78" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	78	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(f a + f b) in H1; elpi z_report "hyp.2g" "79" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	79	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H1; elpi z_report "hyp.2g" "80" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	80	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H1; elpi z_report "hyp.2g" "81" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	81	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _) in H1; elpi z_report "hyp.2g" "82" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	82	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in X + _) in H1; elpi z_report "hyp.2g" "83" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	83	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _ as X in X + _) in H1; elpi z_report "hyp.2g" "84" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	84	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _ in X in X = _) in H1; elpi z_report "hyp.2g" "85" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	85	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _) in H1; elpi z_report "hyp.2g" "86" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	86	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _ as X in X + _ = _) in H1; elpi z_report "hyp.2g" "87" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	87	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(f a) in H1; elpi z_report "hyp.2g" "88" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	88	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(f) in H1; elpi z_report "hyp.2g" "89" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	89	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(f) in H1; elpi z_report "hyp.2g" "90" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	90	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in f X) in H1; elpi z_report "hyp.2g" "91" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	91	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in f X + _) in H1; elpi z_report "hyp.2g" "92" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	92	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in f X + _ = _) in H1; elpi z_report "hyp.2g" "93" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	93	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(a) in H1; elpi z_report "hyp.2g" "94" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	94	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(a) in H1; elpi z_report "hyp.2g" "95" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	95	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ + X) in H1; elpi z_report "hyp.2g" "96" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	96	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f b) in H1; elpi z_report "hyp.2g" "97" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	97	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ + X) in H1; elpi z_report "hyp.2g" "98" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	98	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _) in H1; elpi z_report "hyp.2g" "99" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	99	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f b in X in X = _) in H1; elpi z_report "hyp.2g" "100" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	100	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ + X = _) in H1; elpi z_report "hyp.2g" "101" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	101	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(f b) in H1; elpi z_report "hyp.2g" "102" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	102	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(f) in H1; elpi z_report "hyp.2g" "103" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	103	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(f) in H1; elpi z_report "hyp.2g" "104" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	104	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ + f X) in H1; elpi z_report "hyp.2g" "105" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	105	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ + f X = _) in H1; elpi z_report "hyp.2g" "106" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	106	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(b) in H1; elpi z_report "hyp.2g" "107" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	107	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(b) in H1; elpi z_report "hyp.2g" "108" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	108	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ = X) in H1; elpi z_report "hyp.2g" "109" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	109	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ = X) in H1; elpi z_report "hyp.2g" "110" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	110	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f (a + b)) in H1; elpi z_report "hyp.2g" "111" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	111	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(f (a + b)) in H1; elpi z_report "hyp.2g" "112" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	112	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (f) in H1; elpi z_report "hyp.2g" "113" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	113	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {3}(f) in H1; elpi z_report "hyp.2g" "114" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	114	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {3}(f) in H1; elpi z_report "hyp.2g" "115" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	115	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (a + _) in H1; elpi z_report "hyp.2g" "116" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	116	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X) in H1; elpi z_report "hyp.2g" "117" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	117	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ = X) in H1; elpi z_report "hyp.2g" "118" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	118	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ = f X) in H1; elpi z_report "hyp.2g" "119" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	119	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = f X) in H1; elpi z_report "hyp.2g" "120" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	120	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {1}(a + b) in H1; elpi z_report "hyp.2g" "121" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	121	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (Nat.add) in H1; elpi z_report "hyp.2g" "122" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	122	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add) in H1; elpi z_report "hyp.2g" "123" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	123	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add) in H1; elpi z_report "hyp.2g" "124" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	124	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in X + b) in H1; elpi z_report "hyp.2g" "125" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	125	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in f (X + _)) in H1; elpi z_report "hyp.2g" "126" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	126	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ = f (X + _)) in H1; elpi z_report "hyp.2g" "127" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	127	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (a) in H1; elpi z_report "hyp.2g" "128" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	128	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(a) in H1; elpi z_report "hyp.2g" "129" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	129	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(a) in H1; elpi z_report "hyp.2g" "130" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	130	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in a + X) in H1; elpi z_report "hyp.2g" "131" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	131	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X)) in H1; elpi z_report "hyp.2g" "132" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	132	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (X in _ = f (_ + X)) in H1; elpi z_report "hyp.2g" "133" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	133	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := (b) in H1; elpi z_report "hyp.2g" "134" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	134	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(b) in H1; elpi z_report "hyp.2g" "135" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	135	error" ].
let G := type of H1 in first [ assert_succeeds (set pattern_select_z := {2}(b) in H1; elpi z_report "hyp.2g" "136" ltac_term:(G) "H1") | idtac "SSR	hyp.2g	136	error" ].
Abort.

(* projections, canonical structures (paper, section 3.1): outside the
   fragment for the projection; a concrete operation is a constant *)
Structure monoid := Monoid { mT : Type; mop : mT -> mT -> mT }.
Canonical nat_monoid := Monoid nat plus.
Goal forall a b : nat, mop nat_monoid a b = a + b.
intros a b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mop _ _ _); elpi z_report "proj.1" "1" ltac_term:(G)) | idtac "SSR	proj.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mop _ a _); elpi z_report "proj.1" "2" ltac_term:(G)) | idtac "SSR	proj.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "proj.1" "3" ltac_term:(G)) | idtac "SSR	proj.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (plus _ _); elpi z_report "proj.1" "4" ltac_term:(G)) | idtac "SSR	proj.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mop _ X _); elpi z_report "proj.1" "5" ltac_term:(G)) | idtac "SSR	proj.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "proj.1g" "1" ltac_term:(G)) | idtac "SSR	proj.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mop nat_monoid a b = a + b); elpi z_report "proj.1g" "2" ltac_term:(G)) | idtac "SSR	proj.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "proj.1g" "3" ltac_term:(G)) | idtac "SSR	proj.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "proj.1g" "4" ltac_term:(G)) | idtac "SSR	proj.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mT _); elpi z_report "proj.1g" "5" ltac_term:(G)) | idtac "SSR	proj.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mT nat_monoid); elpi z_report "proj.1g" "6" ltac_term:(G)) | idtac "SSR	proj.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mT); elpi z_report "proj.1g" "7" ltac_term:(G)) | idtac "SSR	proj.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mT); elpi z_report "proj.1g" "8" ltac_term:(G)) | idtac "SSR	proj.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mT X); elpi z_report "proj.1g" "9" ltac_term:(G)) | idtac "SSR	proj.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat_monoid); elpi z_report "proj.1g" "10" ltac_term:(G)) | idtac "SSR	proj.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat_monoid); elpi z_report "proj.1g" "11" ltac_term:(G)) | idtac "SSR	proj.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mop _ _ _); elpi z_report "proj.1g" "12" ltac_term:(G)) | idtac "SSR	proj.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "proj.1g" "13" ltac_term:(G)) | idtac "SSR	proj.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mop _ _ _ as X in X = _); elpi z_report "proj.1g" "14" ltac_term:(G)) | idtac "SSR	proj.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mop nat_monoid a b); elpi z_report "proj.1g" "15" ltac_term:(G)) | idtac "SSR	proj.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mop); elpi z_report "proj.1g" "16" ltac_term:(G)) | idtac "SSR	proj.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mop); elpi z_report "proj.1g" "17" ltac_term:(G)) | idtac "SSR	proj.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mop X _ _); elpi z_report "proj.1g" "18" ltac_term:(G)) | idtac "SSR	proj.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat_monoid); elpi z_report "proj.1g" "19" ltac_term:(G)) | idtac "SSR	proj.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mop X _ _ = _); elpi z_report "proj.1g" "20" ltac_term:(G)) | idtac "SSR	proj.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat_monoid); elpi z_report "proj.1g" "21" ltac_term:(G)) | idtac "SSR	proj.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat_monoid); elpi z_report "proj.1g" "22" ltac_term:(G)) | idtac "SSR	proj.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in mop X _ _ = _); elpi z_report "proj.1g" "23" ltac_term:(G)) | idtac "SSR	proj.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mop _ X _); elpi z_report "proj.1g" "24" ltac_term:(G)) | idtac "SSR	proj.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mop _ X _ = _); elpi z_report "proj.1g" "25" ltac_term:(G)) | idtac "SSR	proj.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "proj.1g" "26" ltac_term:(G)) | idtac "SSR	proj.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "proj.1g" "27" ltac_term:(G)) | idtac "SSR	proj.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mop _ _ X); elpi z_report "proj.1g" "28" ltac_term:(G)) | idtac "SSR	proj.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in mop _ _ X = _); elpi z_report "proj.1g" "29" ltac_term:(G)) | idtac "SSR	proj.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "proj.1g" "30" ltac_term:(G)) | idtac "SSR	proj.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "proj.1g" "31" ltac_term:(G)) | idtac "SSR	proj.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "proj.1g" "32" ltac_term:(G)) | idtac "SSR	proj.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "proj.1g" "33" ltac_term:(G)) | idtac "SSR	proj.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "proj.1g" "34" ltac_term:(G)) | idtac "SSR	proj.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "proj.1g" "35" ltac_term:(G)) | idtac "SSR	proj.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "proj.1g" "36" ltac_term:(G)) | idtac "SSR	proj.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "proj.1g" "37" ltac_term:(G)) | idtac "SSR	proj.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "proj.1g" "38" ltac_term:(G)) | idtac "SSR	proj.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "proj.1g" "39" ltac_term:(G)) | idtac "SSR	proj.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "proj.1g" "40" ltac_term:(G)) | idtac "SSR	proj.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "proj.1g" "41" ltac_term:(G)) | idtac "SSR	proj.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "proj.1g" "42" ltac_term:(G)) | idtac "SSR	proj.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "proj.1g" "43" ltac_term:(G)) | idtac "SSR	proj.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "proj.1g" "44" ltac_term:(G)) | idtac "SSR	proj.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "proj.1g" "45" ltac_term:(G)) | idtac "SSR	proj.1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "proj.1g" "46" ltac_term:(G)) | idtac "SSR	proj.1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "proj.1g" "47" ltac_term:(G)) | idtac "SSR	proj.1g	47	error" ].
Abort.

(* flexible head and other forms outside the fragment *)
Goal forall (f g : nat -> nat) a, f a = g a.
intros f g a.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ a); elpi z_report "outside.1" "1" ltac_term:(G)) | idtac "SSR	outside.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X a = _); elpi z_report "outside.1" "2" ltac_term:(G)) | idtac "SSR	outside.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X); elpi z_report "outside.1" "3" ltac_term:(G)) | idtac "SSR	outside.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (let x := a in x); elpi z_report "outside.1" "4" ltac_term:(G)) | idtac "SSR	outside.1	4	error" ].
Abort.

(* failures: no instance, a closed term that does not occur, X absent *)
Goal forall a b : nat, a + b = b + a.
intros a b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "fail.1" "1" ltac_term:(G)) | idtac "SSR	fail.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a * b); elpi z_report "fail.1" "2" ltac_term:(G)) | idtac "SSR	fail.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "fail.1" "3" ltac_term:(G)) | idtac "SSR	fail.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ = X); elpi z_report "fail.1" "4" ltac_term:(G)) | idtac "SSR	fail.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + a); elpi z_report "fail.1" "5" ltac_term:(G)) | idtac "SSR	fail.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + a); elpi z_report "fail.1" "6" ltac_term:(G)) | idtac "SSR	fail.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + _); elpi z_report "fail.1" "7" ltac_term:(G)) | idtac "SSR	fail.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + a in X in X = _); elpi z_report "fail.1" "8" ltac_term:(G)) | idtac "SSR	fail.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ + _); elpi z_report "fail.1" "9" ltac_term:(G)) | idtac "SSR	fail.1	9	error" ].
Abort.

(* a match, a let, an if *)
Goal forall (n : nat) (b : bool), (if b then n else 0) = match n with 0 => 1 | S k => k end /\ (let x := n in x + x) = n.
intros n b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (if _ then _ else _); elpi z_report "match.1" "1" ltac_term:(G)) | idtac "SSR	match.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "match.1" "2" ltac_term:(G)) | idtac "SSR	match.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "match.1" "3" ltac_term:(G)) | idtac "SSR	match.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (if _ then X else _) = _); elpi z_report "match.1" "4" ltac_term:(G)) | idtac "SSR	match.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "match.1" "5" ltac_term:(G)) | idtac "SSR	match.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "match.1" "6" ltac_term:(G)) | idtac "SSR	match.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "match.1" "7" ltac_term:(G)) | idtac "SSR	match.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "match.1" "8" ltac_term:(G)) | idtac "SSR	match.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (let x := X in _) = _); elpi z_report "match.1" "9" ltac_term:(G)) | idtac "SSR	match.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "match.1g" "1" ltac_term:(G)) | idtac "SSR	match.1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((if b then n else 0) = match n with | 0 => 1 | S k => k end /\ (let x := n in x + x) = n); elpi z_report "match.1g" "2" ltac_term:(G)) | idtac "SSR	match.1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "match.1g" "3" ltac_term:(G)) | idtac "SSR	match.1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "match.1g" "4" ltac_term:(G)) | idtac "SSR	match.1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "match.1g" "5" ltac_term:(G)) | idtac "SSR	match.1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "match.1g" "6" ltac_term:(G)) | idtac "SSR	match.1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "match.1g" "7" ltac_term:(G)) | idtac "SSR	match.1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((if b then n else 0) = match n with | 0 => 1 | S k => k end); elpi z_report "match.1g" "8" ltac_term:(G)) | idtac "SSR	match.1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "match.1g" "9" ltac_term:(G)) | idtac "SSR	match.1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "match.1g" "10" ltac_term:(G)) | idtac "SSR	match.1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "match.1g" "11" ltac_term:(G)) | idtac "SSR	match.1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "match.1g" "12" ltac_term:(G)) | idtac "SSR	match.1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "match.1g" "13" ltac_term:(G)) | idtac "SSR	match.1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "match.1g" "14" ltac_term:(G)) | idtac "SSR	match.1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (if b then n else 0); elpi z_report "match.1g" "15" ltac_term:(G)) | idtac "SSR	match.1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(if b then n else 0); elpi z_report "match.1g" "16" ltac_term:(G)) | idtac "SSR	match.1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "match.1g" "17" ltac_term:(G)) | idtac "SSR	match.1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "match.1g" "18" ltac_term:(G)) | idtac "SSR	match.1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "match.1g" "19" ltac_term:(G)) | idtac "SSR	match.1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "match.1g" "20" ltac_term:(G)) | idtac "SSR	match.1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "match.1g" "21" ltac_term:(G)) | idtac "SSR	match.1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "match.1g" "22" ltac_term:(G)) | idtac "SSR	match.1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "match.1g" "23" ltac_term:(G)) | idtac "SSR	match.1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "match.1g" "24" ltac_term:(G)) | idtac "SSR	match.1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "match.1g" "25" ltac_term:(G)) | idtac "SSR	match.1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "match.1g" "26" ltac_term:(G)) | idtac "SSR	match.1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (match n with | 0 => 1 | S k => k end); elpi z_report "match.1g" "27" ltac_term:(G)) | idtac "SSR	match.1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(match n with | 0 => 1 | S k => k end); elpi z_report "match.1g" "28" ltac_term:(G)) | idtac "SSR	match.1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "match.1g" "29" ltac_term:(G)) | idtac "SSR	match.1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "match.1g" "30" ltac_term:(G)) | idtac "SSR	match.1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "match.1g" "31" ltac_term:(G)) | idtac "SSR	match.1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "match.1g" "32" ltac_term:(G)) | idtac "SSR	match.1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "match.1g" "33" ltac_term:(G)) | idtac "SSR	match.1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X); elpi z_report "match.1g" "34" ltac_term:(G)) | idtac "SSR	match.1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X /\ _); elpi z_report "match.1g" "35" ltac_term:(G)) | idtac "SSR	match.1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X /\ _); elpi z_report "match.1g" "36" ltac_term:(G)) | idtac "SSR	match.1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "match.1g" "37" ltac_term:(G)) | idtac "SSR	match.1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "match.1g" "38" ltac_term:(G)) | idtac "SSR	match.1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "match.1g" "39" ltac_term:(G)) | idtac "SSR	match.1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "match.1g" "40" ltac_term:(G)) | idtac "SSR	match.1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "match.1g" "41" ltac_term:(G)) | idtac "SSR	match.1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "match.1g" "42" ltac_term:(G)) | idtac "SSR	match.1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "match.1g" "43" ltac_term:(G)) | idtac "SSR	match.1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "match.1g" "44" ltac_term:(G)) | idtac "SSR	match.1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "match.1g" "45" ltac_term:(G)) | idtac "SSR	match.1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((let x := n in x + x) = _); elpi z_report "match.1g" "46" ltac_term:(G)) | idtac "SSR	match.1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((let x := n in x + x) = n); elpi z_report "match.1g" "47" ltac_term:(G)) | idtac "SSR	match.1g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "match.1g" "48" ltac_term:(G)) | idtac "SSR	match.1g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "match.1g" "49" ltac_term:(G)) | idtac "SSR	match.1g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "match.1g" "50" ltac_term:(G)) | idtac "SSR	match.1g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "match.1g" "51" ltac_term:(G)) | idtac "SSR	match.1g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "match.1g" "52" ltac_term:(G)) | idtac "SSR	match.1g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = n); elpi z_report "match.1g" "53" ltac_term:(G)) | idtac "SSR	match.1g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "match.1g" "54" ltac_term:(G)) | idtac "SSR	match.1g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "match.1g" "55" ltac_term:(G)) | idtac "SSR	match.1g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(nat); elpi z_report "match.1g" "56" ltac_term:(G)) | idtac "SSR	match.1g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(nat); elpi z_report "match.1g" "57" ltac_term:(G)) | idtac "SSR	match.1g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "match.1g" "58" ltac_term:(G)) | idtac "SSR	match.1g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "match.1g" "59" ltac_term:(G)) | idtac "SSR	match.1g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "match.1g" "60" ltac_term:(G)) | idtac "SSR	match.1g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "match.1g" "61" ltac_term:(G)) | idtac "SSR	match.1g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "match.1g" "62" ltac_term:(G)) | idtac "SSR	match.1g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (let x := n in x + x) = X); elpi z_report "match.1g" "63" ltac_term:(G)) | idtac "SSR	match.1g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "match.1g" "64" ltac_term:(G)) | idtac "SSR	match.1g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "match.1g" "65" ltac_term:(G)) | idtac "SSR	match.1g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "match.1g" "66" ltac_term:(G)) | idtac "SSR	match.1g	66	error" ].
Abort.

(* a hypothesis: set in H generalizes H over the conclusion *)
Goal forall a : nat, a + 0 = 0 -> (forall n : nat, n = n) -> a + 0 = a.
intros a H H'.
let G := type of H in first [ assert_succeeds (set pattern_select_z := (a + 0) in H; elpi z_report "hyp.4" "1" ltac_term:(G) "H") | idtac "SSR	hyp.4	1	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(a + 0) in H; elpi z_report "hyp.4" "2" ltac_term:(G) "H") | idtac "SSR	hyp.4	2	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(a + 0) in H; elpi z_report "hyp.4" "3" ltac_term:(G) "H") | idtac "SSR	hyp.4	3	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ = _) in H; elpi z_report "hyp.4" "4" ltac_term:(G) "H") | idtac "SSR	hyp.4	4	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(_ = _) in H; elpi z_report "hyp.4" "5" ltac_term:(G) "H") | idtac "SSR	hyp.4	5	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in X = _) in H; elpi z_report "hyp.4" "6" ltac_term:(G) "H") | idtac "SSR	hyp.4	6	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := (forall n, _) in H'; elpi z_report "hyp.5" "1" ltac_term:(G) "H'") | idtac "SSR	hyp.5	1	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := (_ = _) in H'; elpi z_report "hyp.5" "2" ltac_term:(G) "H'") | idtac "SSR	hyp.5	2	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := (nat) in H'; elpi z_report "hyp.5" "3" ltac_term:(G) "H'") | idtac "SSR	hyp.5	3	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := {2}(_ = _) in H'; elpi z_report "hyp.5" "4" ltac_term:(G) "H'") | idtac "SSR	hyp.5	4	error" ].
Abort.
