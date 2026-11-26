(* Differential corpus: the goals of point_paths_test.v, with every pattern
   that select_all and point_to_pattern produce for every path.  Run by
   run.sh. *)
From Stdlib Require Import String.
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support.

Definition double n := n + n.

Goal forall a : nat, 1 + 1 + a = double (1 + a).
intros a.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.1" "1" ltac_term:(G)) | idtac "SSR	pp.1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + 1 + a = double (1 + a)); elpi z_report "pp.1" "2" ltac_term:(G)) | idtac "SSR	pp.1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.1" "3" ltac_term:(G)) | idtac "SSR	pp.1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.1" "4" ltac_term:(G)) | idtac "SSR	pp.1	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.1" "5" ltac_term:(G)) | idtac "SSR	pp.1	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.1" "6" ltac_term:(G)) | idtac "SSR	pp.1	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "pp.1" "7" ltac_term:(G)) | idtac "SSR	pp.1	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.1" "8" ltac_term:(G)) | idtac "SSR	pp.1	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "pp.1" "9" ltac_term:(G)) | idtac "SSR	pp.1	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + 1 + a); elpi z_report "pp.1" "10" ltac_term:(G)) | idtac "SSR	pp.1	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.1" "11" ltac_term:(G)) | idtac "SSR	pp.1	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.1" "12" ltac_term:(G)) | idtac "SSR	pp.1	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "pp.1" "13" ltac_term:(G)) | idtac "SSR	pp.1	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _); elpi z_report "pp.1" "14" ltac_term:(G)) | idtac "SSR	pp.1	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "pp.1" "15" ltac_term:(G)) | idtac "SSR	pp.1	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "pp.1" "16" ltac_term:(G)) | idtac "SSR	pp.1	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _ in X in X = _); elpi z_report "pp.1" "17" ltac_term:(G)) | idtac "SSR	pp.1	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "pp.1" "18" ltac_term:(G)) | idtac "SSR	pp.1	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + 1); elpi z_report "pp.1" "19" ltac_term:(G)) | idtac "SSR	pp.1	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "pp.1" "20" ltac_term:(G)) | idtac "SSR	pp.1	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "pp.1" "21" ltac_term:(G)) | idtac "SSR	pp.1	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + 1); elpi z_report "pp.1" "22" ltac_term:(G)) | idtac "SSR	pp.1	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _); elpi z_report "pp.1" "23" ltac_term:(G)) | idtac "SSR	pp.1	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "pp.1" "24" ltac_term:(G)) | idtac "SSR	pp.1	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ + _); elpi z_report "pp.1" "25" ltac_term:(G)) | idtac "SSR	pp.1	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "pp.1" "26" ltac_term:(G)) | idtac "SSR	pp.1	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ + _ = _); elpi z_report "pp.1" "27" ltac_term:(G)) | idtac "SSR	pp.1	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "pp.1" "28" ltac_term:(G)) | idtac "SSR	pp.1	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "pp.1" "29" ltac_term:(G)) | idtac "SSR	pp.1	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X = _); elpi z_report "pp.1" "30" ltac_term:(G)) | idtac "SSR	pp.1	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X + _); elpi z_report "pp.1" "31" ltac_term:(G)) | idtac "SSR	pp.1	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X + _ = _); elpi z_report "pp.1" "32" ltac_term:(G)) | idtac "SSR	pp.1	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.1" "33" ltac_term:(G)) | idtac "SSR	pp.1	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.1" "34" ltac_term:(G)) | idtac "SSR	pp.1	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _); elpi z_report "pp.1" "35" ltac_term:(G)) | idtac "SSR	pp.1	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ + _); elpi z_report "pp.1" "36" ltac_term:(G)) | idtac "SSR	pp.1	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ + _ = _); elpi z_report "pp.1" "37" ltac_term:(G)) | idtac "SSR	pp.1	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.1" "38" ltac_term:(G)) | idtac "SSR	pp.1	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.1" "39" ltac_term:(G)) | idtac "SSR	pp.1	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "pp.1" "40" ltac_term:(G)) | idtac "SSR	pp.1	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + X); elpi z_report "pp.1" "41" ltac_term:(G)) | idtac "SSR	pp.1	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X); elpi z_report "pp.1" "42" ltac_term:(G)) | idtac "SSR	pp.1	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "pp.1" "43" ltac_term:(G)) | idtac "SSR	pp.1	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X + _); elpi z_report "pp.1" "44" ltac_term:(G)) | idtac "SSR	pp.1	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "pp.1" "45" ltac_term:(G)) | idtac "SSR	pp.1	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X + _ = _); elpi z_report "pp.1" "46" ltac_term:(G)) | idtac "SSR	pp.1	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "pp.1" "47" ltac_term:(G)) | idtac "SSR	pp.1	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + _); elpi z_report "pp.1" "48" ltac_term:(G)) | idtac "SSR	pp.1	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + _ = _); elpi z_report "pp.1" "49" ltac_term:(G)) | idtac "SSR	pp.1	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "pp.1" "50" ltac_term:(G)) | idtac "SSR	pp.1	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "pp.1" "51" ltac_term:(G)) | idtac "SSR	pp.1	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X = _); elpi z_report "pp.1" "52" ltac_term:(G)) | idtac "SSR	pp.1	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X + _); elpi z_report "pp.1" "53" ltac_term:(G)) | idtac "SSR	pp.1	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X + _ = _); elpi z_report "pp.1" "54" ltac_term:(G)) | idtac "SSR	pp.1	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.1" "55" ltac_term:(G)) | idtac "SSR	pp.1	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.1" "56" ltac_term:(G)) | idtac "SSR	pp.1	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X); elpi z_report "pp.1" "57" ltac_term:(G)) | idtac "SSR	pp.1	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X + _); elpi z_report "pp.1" "58" ltac_term:(G)) | idtac "SSR	pp.1	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X + _ = _); elpi z_report "pp.1" "59" ltac_term:(G)) | idtac "SSR	pp.1	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.1" "60" ltac_term:(G)) | idtac "SSR	pp.1	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.1" "61" ltac_term:(G)) | idtac "SSR	pp.1	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X); elpi z_report "pp.1" "62" ltac_term:(G)) | idtac "SSR	pp.1	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "pp.1" "63" ltac_term:(G)) | idtac "SSR	pp.1	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "pp.1" "64" ltac_term:(G)) | idtac "SSR	pp.1	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.1" "65" ltac_term:(G)) | idtac "SSR	pp.1	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.1" "66" ltac_term:(G)) | idtac "SSR	pp.1	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double _); elpi z_report "pp.1" "67" ltac_term:(G)) | idtac "SSR	pp.1	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.1" "68" ltac_term:(G)) | idtac "SSR	pp.1	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double _ as X in _ = X); elpi z_report "pp.1" "69" ltac_term:(G)) | idtac "SSR	pp.1	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(double (1 + a)); elpi z_report "pp.1" "70" ltac_term:(G)) | idtac "SSR	pp.1	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double); elpi z_report "pp.1" "71" ltac_term:(G)) | idtac "SSR	pp.1	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(double); elpi z_report "pp.1" "72" ltac_term:(G)) | idtac "SSR	pp.1	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double X); elpi z_report "pp.1" "73" ltac_term:(G)) | idtac "SSR	pp.1	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ = X); elpi z_report "pp.1" "74" ltac_term:(G)) | idtac "SSR	pp.1	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in double X); elpi z_report "pp.1" "75" ltac_term:(G)) | idtac "SSR	pp.1	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = double X); elpi z_report "pp.1" "76" ltac_term:(G)) | idtac "SSR	pp.1	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + a); elpi z_report "pp.1" "77" ltac_term:(G)) | idtac "SSR	pp.1	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = double X); elpi z_report "pp.1" "78" ltac_term:(G)) | idtac "SSR	pp.1	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + a); elpi z_report "pp.1" "79" ltac_term:(G)) | idtac "SSR	pp.1	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.1" "80" ltac_term:(G)) | idtac "SSR	pp.1	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "pp.1" "81" ltac_term:(G)) | idtac "SSR	pp.1	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "pp.1" "82" ltac_term:(G)) | idtac "SSR	pp.1	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X); elpi z_report "pp.1" "83" ltac_term:(G)) | idtac "SSR	pp.1	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in double X); elpi z_report "pp.1" "84" ltac_term:(G)) | idtac "SSR	pp.1	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double (X + _)); elpi z_report "pp.1" "85" ltac_term:(G)) | idtac "SSR	pp.1	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + a); elpi z_report "pp.1" "86" ltac_term:(G)) | idtac "SSR	pp.1	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = double X); elpi z_report "pp.1" "87" ltac_term:(G)) | idtac "SSR	pp.1	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in double (X + _)); elpi z_report "pp.1" "88" ltac_term:(G)) | idtac "SSR	pp.1	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = double (X + _)); elpi z_report "pp.1" "89" ltac_term:(G)) | idtac "SSR	pp.1	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = double (X + _)); elpi z_report "pp.1" "90" ltac_term:(G)) | idtac "SSR	pp.1	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "pp.1" "91" ltac_term:(G)) | idtac "SSR	pp.1	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "pp.1" "92" ltac_term:(G)) | idtac "SSR	pp.1	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _); elpi z_report "pp.1" "93" ltac_term:(G)) | idtac "SSR	pp.1	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "pp.1" "94" ltac_term:(G)) | idtac "SSR	pp.1	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "pp.1" "95" ltac_term:(G)) | idtac "SSR	pp.1	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "pp.1" "96" ltac_term:(G)) | idtac "SSR	pp.1	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + a); elpi z_report "pp.1" "97" ltac_term:(G)) | idtac "SSR	pp.1	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double (S X + _)); elpi z_report "pp.1" "98" ltac_term:(G)) | idtac "SSR	pp.1	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = double (S X + _)); elpi z_report "pp.1" "99" ltac_term:(G)) | idtac "SSR	pp.1	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.1" "100" ltac_term:(G)) | idtac "SSR	pp.1	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "pp.1" "101" ltac_term:(G)) | idtac "SSR	pp.1	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "pp.1" "102" ltac_term:(G)) | idtac "SSR	pp.1	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "pp.1" "103" ltac_term:(G)) | idtac "SSR	pp.1	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S X); elpi z_report "pp.1" "104" ltac_term:(G)) | idtac "SSR	pp.1	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double (_ + X)); elpi z_report "pp.1" "105" ltac_term:(G)) | idtac "SSR	pp.1	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = double (_ + X)); elpi z_report "pp.1" "106" ltac_term:(G)) | idtac "SSR	pp.1	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "pp.1" "107" ltac_term:(G)) | idtac "SSR	pp.1	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "pp.1" "108" ltac_term:(G)) | idtac "SSR	pp.1	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "pp.1" "109" ltac_term:(G)) | idtac "SSR	pp.1	109	error" ].
Abort.

Goal forall a b : nat, a = b -> b = a.
intros a b ab.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.2" "1" ltac_term:(G)) | idtac "SSR	pp.2	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b = a); elpi z_report "pp.2" "2" ltac_term:(G)) | idtac "SSR	pp.2	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.2" "3" ltac_term:(G)) | idtac "SSR	pp.2	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.2" "4" ltac_term:(G)) | idtac "SSR	pp.2	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.2" "5" ltac_term:(G)) | idtac "SSR	pp.2	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.2" "6" ltac_term:(G)) | idtac "SSR	pp.2	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.2" "7" ltac_term:(G)) | idtac "SSR	pp.2	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.2" "8" ltac_term:(G)) | idtac "SSR	pp.2	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.2" "9" ltac_term:(G)) | idtac "SSR	pp.2	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "pp.2" "10" ltac_term:(G)) | idtac "SSR	pp.2	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.2" "11" ltac_term:(G)) | idtac "SSR	pp.2	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.2" "12" ltac_term:(G)) | idtac "SSR	pp.2	12	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := (_ = _) in ab; elpi z_report "pp.2" "13" ltac_term:(G) "ab") | idtac "SSR	pp.2	13	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := {1}(a = b) in ab; elpi z_report "pp.2" "14" ltac_term:(G) "ab") | idtac "SSR	pp.2	14	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := (@eq) in ab; elpi z_report "pp.2" "15" ltac_term:(G) "ab") | idtac "SSR	pp.2	15	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in ab; elpi z_report "pp.2" "16" ltac_term:(G) "ab") | idtac "SSR	pp.2	16	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := (nat) in ab; elpi z_report "pp.2" "17" ltac_term:(G) "ab") | idtac "SSR	pp.2	17	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := {1}(nat) in ab; elpi z_report "pp.2" "18" ltac_term:(G) "ab") | idtac "SSR	pp.2	18	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := (a) in ab; elpi z_report "pp.2" "19" ltac_term:(G) "ab") | idtac "SSR	pp.2	19	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := (X in X = _) in ab; elpi z_report "pp.2" "20" ltac_term:(G) "ab") | idtac "SSR	pp.2	20	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := {1}(a) in ab; elpi z_report "pp.2" "21" ltac_term:(G) "ab") | idtac "SSR	pp.2	21	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := (b) in ab; elpi z_report "pp.2" "22" ltac_term:(G) "ab") | idtac "SSR	pp.2	22	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := (X in _ = X) in ab; elpi z_report "pp.2" "23" ltac_term:(G) "ab") | idtac "SSR	pp.2	23	error" ].
let G := type of ab in first [ assert_succeeds (set pattern_select_z := {1}(b) in ab; elpi z_report "pp.2" "24" ltac_term:(G) "ab") | idtac "SSR	pp.2	24	error" ].
Abort.

Goal ("a b" = "a b")%string.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.3" "1" ltac_term:(G)) | idtac "SSR	pp.3	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}("a b"%string = "a b"%string); elpi z_report "pp.3" "2" ltac_term:(G)) | idtac "SSR	pp.3	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.3" "3" ltac_term:(G)) | idtac "SSR	pp.3	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.3" "4" ltac_term:(G)) | idtac "SSR	pp.3	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (string); elpi z_report "pp.3" "5" ltac_term:(G)) | idtac "SSR	pp.3	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(string); elpi z_report "pp.3" "6" ltac_term:(G)) | idtac "SSR	pp.3	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.3" "7" ltac_term:(G)) | idtac "SSR	pp.3	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in X = _); elpi z_report "pp.3" "8" ltac_term:(G)) | idtac "SSR	pp.3	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _); elpi z_report "pp.3" "9" ltac_term:(G)) | idtac "SSR	pp.3	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String _ _); elpi z_report "pp.3" "10" ltac_term:(G)) | idtac "SSR	pp.3	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}("a b"%string); elpi z_report "pp.3" "11" ltac_term:(G)) | idtac "SSR	pp.3	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String); elpi z_report "pp.3" "12" ltac_term:(G)) | idtac "SSR	pp.3	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String); elpi z_report "pp.3" "13" ltac_term:(G)) | idtac "SSR	pp.3	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in X = _); elpi z_report "pp.3" "14" ltac_term:(G)) | idtac "SSR	pp.3	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String X _ = _); elpi z_report "pp.3" "15" ltac_term:(G)) | idtac "SSR	pp.3	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in String X _ = _); elpi z_report "pp.3" "16" ltac_term:(G)) | idtac "SSR	pp.3	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _); elpi z_report "pp.3" "17" ltac_term:(G)) | idtac "SSR	pp.3	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String X _); elpi z_report "pp.3" "18" ltac_term:(G)) | idtac "SSR	pp.3	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "19" ltac_term:(G)) | idtac "SSR	pp.3	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ _ _ _ _ _ _ _); elpi z_report "pp.3" "20" ltac_term:(G)) | idtac "SSR	pp.3	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String X _); elpi z_report "pp.3" "21" ltac_term:(G)) | idtac "SSR	pp.3	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ _ _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "22" ltac_term:(G)) | idtac "SSR	pp.3	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii true false false false false true true false); elpi z_report "pp.3" "23" ltac_term:(G)) | idtac "SSR	pp.3	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii); elpi z_report "pp.3" "24" ltac_term:(G)) | idtac "SSR	pp.3	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii); elpi z_report "pp.3" "25" ltac_term:(G)) | idtac "SSR	pp.3	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii X _ _ _ _ _ _ _) _ = _); elpi z_report "pp.3" "26" ltac_term:(G)) | idtac "SSR	pp.3	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii X _ _ _ _ _ _ _); elpi z_report "pp.3" "27" ltac_term:(G)) | idtac "SSR	pp.3	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii X _ _ _ _ _ _ _) _); elpi z_report "pp.3" "28" ltac_term:(G)) | idtac "SSR	pp.3	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.3" "29" ltac_term:(G)) | idtac "SSR	pp.3	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.3" "30" ltac_term:(G)) | idtac "SSR	pp.3	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii X _ _ _ _ _ _ _); elpi z_report "pp.3" "31" ltac_term:(G)) | idtac "SSR	pp.3	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii X _ _ _ _ _ _ _) _); elpi z_report "pp.3" "32" ltac_term:(G)) | idtac "SSR	pp.3	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ X _ _ _ _ _ _) _ = _); elpi z_report "pp.3" "33" ltac_term:(G)) | idtac "SSR	pp.3	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ X _ _ _ _ _ _); elpi z_report "pp.3" "34" ltac_term:(G)) | idtac "SSR	pp.3	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ X _ _ _ _ _ _) _); elpi z_report "pp.3" "35" ltac_term:(G)) | idtac "SSR	pp.3	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(false); elpi z_report "pp.3" "36" ltac_term:(G)) | idtac "SSR	pp.3	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(false); elpi z_report "pp.3" "37" ltac_term:(G)) | idtac "SSR	pp.3	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ X _ _ _ _ _ _); elpi z_report "pp.3" "38" ltac_term:(G)) | idtac "SSR	pp.3	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ X _ _ _ _ _ _) _); elpi z_report "pp.3" "39" ltac_term:(G)) | idtac "SSR	pp.3	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ X _ _ _ _ _) _ = _); elpi z_report "pp.3" "40" ltac_term:(G)) | idtac "SSR	pp.3	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ X _ _ _ _ _); elpi z_report "pp.3" "41" ltac_term:(G)) | idtac "SSR	pp.3	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ X _ _ _ _ _) _); elpi z_report "pp.3" "42" ltac_term:(G)) | idtac "SSR	pp.3	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(false); elpi z_report "pp.3" "43" ltac_term:(G)) | idtac "SSR	pp.3	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(false); elpi z_report "pp.3" "44" ltac_term:(G)) | idtac "SSR	pp.3	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ _ X _ _ _ _ _); elpi z_report "pp.3" "45" ltac_term:(G)) | idtac "SSR	pp.3	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ _ X _ _ _ _ _) _); elpi z_report "pp.3" "46" ltac_term:(G)) | idtac "SSR	pp.3	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ X _ _ _ _) _ = _); elpi z_report "pp.3" "47" ltac_term:(G)) | idtac "SSR	pp.3	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ X _ _ _ _); elpi z_report "pp.3" "48" ltac_term:(G)) | idtac "SSR	pp.3	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ X _ _ _ _) _); elpi z_report "pp.3" "49" ltac_term:(G)) | idtac "SSR	pp.3	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(false); elpi z_report "pp.3" "50" ltac_term:(G)) | idtac "SSR	pp.3	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(false); elpi z_report "pp.3" "51" ltac_term:(G)) | idtac "SSR	pp.3	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ _ _ X _ _ _ _); elpi z_report "pp.3" "52" ltac_term:(G)) | idtac "SSR	pp.3	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ _ _ X _ _ _ _) _); elpi z_report "pp.3" "53" ltac_term:(G)) | idtac "SSR	pp.3	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ X _ _ _) _ = _); elpi z_report "pp.3" "54" ltac_term:(G)) | idtac "SSR	pp.3	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ _ X _ _ _); elpi z_report "pp.3" "55" ltac_term:(G)) | idtac "SSR	pp.3	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ X _ _ _) _); elpi z_report "pp.3" "56" ltac_term:(G)) | idtac "SSR	pp.3	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(false); elpi z_report "pp.3" "57" ltac_term:(G)) | idtac "SSR	pp.3	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(false); elpi z_report "pp.3" "58" ltac_term:(G)) | idtac "SSR	pp.3	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ _ _ _ X _ _ _); elpi z_report "pp.3" "59" ltac_term:(G)) | idtac "SSR	pp.3	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ _ _ _ X _ _ _) _); elpi z_report "pp.3" "60" ltac_term:(G)) | idtac "SSR	pp.3	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ X _ _) _ = _); elpi z_report "pp.3" "61" ltac_term:(G)) | idtac "SSR	pp.3	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ _ _ X _ _); elpi z_report "pp.3" "62" ltac_term:(G)) | idtac "SSR	pp.3	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ X _ _) _); elpi z_report "pp.3" "63" ltac_term:(G)) | idtac "SSR	pp.3	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.3" "64" ltac_term:(G)) | idtac "SSR	pp.3	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.3" "65" ltac_term:(G)) | idtac "SSR	pp.3	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ _ _ _ _ X _ _); elpi z_report "pp.3" "66" ltac_term:(G)) | idtac "SSR	pp.3	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ _ _ _ _ X _ _) _); elpi z_report "pp.3" "67" ltac_term:(G)) | idtac "SSR	pp.3	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ _ X _) _ = _); elpi z_report "pp.3" "68" ltac_term:(G)) | idtac "SSR	pp.3	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ _ _ _ X _); elpi z_report "pp.3" "69" ltac_term:(G)) | idtac "SSR	pp.3	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ _ X _) _); elpi z_report "pp.3" "70" ltac_term:(G)) | idtac "SSR	pp.3	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(true); elpi z_report "pp.3" "71" ltac_term:(G)) | idtac "SSR	pp.3	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(true); elpi z_report "pp.3" "72" ltac_term:(G)) | idtac "SSR	pp.3	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ _ _ _ _ _ X _); elpi z_report "pp.3" "73" ltac_term:(G)) | idtac "SSR	pp.3	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ _ _ _ _ _ X _) _); elpi z_report "pp.3" "74" ltac_term:(G)) | idtac "SSR	pp.3	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ _ _ X) _ = _); elpi z_report "pp.3" "75" ltac_term:(G)) | idtac "SSR	pp.3	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ _ _ _ _ X); elpi z_report "pp.3" "76" ltac_term:(G)) | idtac "SSR	pp.3	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ _ _ X) _); elpi z_report "pp.3" "77" ltac_term:(G)) | idtac "SSR	pp.3	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(false); elpi z_report "pp.3" "78" ltac_term:(G)) | idtac "SSR	pp.3	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(false); elpi z_report "pp.3" "79" ltac_term:(G)) | idtac "SSR	pp.3	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ _ _ _ _ _ _ X); elpi z_report "pp.3" "80" ltac_term:(G)) | idtac "SSR	pp.3	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ _ _ _ _ _ _ X) _); elpi z_report "pp.3" "81" ltac_term:(G)) | idtac "SSR	pp.3	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ X = _); elpi z_report "pp.3" "82" ltac_term:(G)) | idtac "SSR	pp.3	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in String _ X = _); elpi z_report "pp.3" "83" ltac_term:(G)) | idtac "SSR	pp.3	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String (Ascii.Ascii false _ _ _ _ _ _ _) _ in X in X = _); elpi z_report "pp.3" "84" ltac_term:(G)) | idtac "SSR	pp.3	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ X); elpi z_report "pp.3" "85" ltac_term:(G)) | idtac "SSR	pp.3	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in String _ X); elpi z_report "pp.3" "86" ltac_term:(G)) | idtac "SSR	pp.3	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String (Ascii.Ascii false _ _ _ _ _ _ _) _); elpi z_report "pp.3" "87" ltac_term:(G)) | idtac "SSR	pp.3	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ X); elpi z_report "pp.3" "88" ltac_term:(G)) | idtac "SSR	pp.3	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(" b"%string); elpi z_report "pp.3" "89" ltac_term:(G)) | idtac "SSR	pp.3	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String _ _ as X in String _ X); elpi z_report "pp.3" "90" ltac_term:(G)) | idtac "SSR	pp.3	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String (Ascii.Ascii false _ _ _ _ _ _ _) _); elpi z_report "pp.3" "91" ltac_term:(G)) | idtac "SSR	pp.3	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String); elpi z_report "pp.3" "92" ltac_term:(G)) | idtac "SSR	pp.3	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String); elpi z_report "pp.3" "93" ltac_term:(G)) | idtac "SSR	pp.3	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii false _ _ _ _ _ _ _ in X in X = _); elpi z_report "pp.3" "94" ltac_term:(G)) | idtac "SSR	pp.3	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in String _ X = _); elpi z_report "pp.3" "95" ltac_term:(G)) | idtac "SSR	pp.3	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String X _) = _); elpi z_report "pp.3" "96" ltac_term:(G)) | idtac "SSR	pp.3	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in String _ (String X _) = _); elpi z_report "pp.3" "97" ltac_term:(G)) | idtac "SSR	pp.3	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii false _ _ _ _ _ _ _); elpi z_report "pp.3" "98" ltac_term:(G)) | idtac "SSR	pp.3	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in String _ X); elpi z_report "pp.3" "99" ltac_term:(G)) | idtac "SSR	pp.3	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String X _)); elpi z_report "pp.3" "100" ltac_term:(G)) | idtac "SSR	pp.3	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii false _ _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "101" ltac_term:(G)) | idtac "SSR	pp.3	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in String _ (String X _)); elpi z_report "pp.3" "102" ltac_term:(G)) | idtac "SSR	pp.3	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii false _ _ _ _ _ _ _); elpi z_report "pp.3" "103" ltac_term:(G)) | idtac "SSR	pp.3	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ _ _ _ _ _ _ _ in X in String _ X); elpi z_report "pp.3" "104" ltac_term:(G)) | idtac "SSR	pp.3	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String X _)); elpi z_report "pp.3" "105" ltac_term:(G)) | idtac "SSR	pp.3	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String X (String _ "")); elpi z_report "pp.3" "106" ltac_term:(G)) | idtac "SSR	pp.3	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii false _ _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "107" ltac_term:(G)) | idtac "SSR	pp.3	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ _ _ _ _ _ _ _ as X in String _ (String X _)); elpi z_report "pp.3" "108" ltac_term:(G)) | idtac "SSR	pp.3	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii false false false false false true false false); elpi z_report "pp.3" "109" ltac_term:(G)) | idtac "SSR	pp.3	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii); elpi z_report "pp.3" "110" ltac_term:(G)) | idtac "SSR	pp.3	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii); elpi z_report "pp.3" "111" ltac_term:(G)) | idtac "SSR	pp.3	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _) = _); elpi z_report "pp.3" "112" ltac_term:(G)) | idtac "SSR	pp.3	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _)); elpi z_report "pp.3" "113" ltac_term:(G)) | idtac "SSR	pp.3	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(false); elpi z_report "pp.3" "114" ltac_term:(G)) | idtac "SSR	pp.3	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(false); elpi z_report "pp.3" "115" ltac_term:(G)) | idtac "SSR	pp.3	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii X _ _ _ _ _ false _); elpi z_report "pp.3" "116" ltac_term:(G)) | idtac "SSR	pp.3	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii X _ _ _ _ _ false _) _); elpi z_report "pp.3" "117" ltac_term:(G)) | idtac "SSR	pp.3	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _)); elpi z_report "pp.3" "118" ltac_term:(G)) | idtac "SSR	pp.3	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _) = _); elpi z_report "pp.3" "119" ltac_term:(G)) | idtac "SSR	pp.3	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false X _ _ _ _ _ _); elpi z_report "pp.3" "120" ltac_term:(G)) | idtac "SSR	pp.3	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false X _ _ _ _ _ _) _); elpi z_report "pp.3" "121" ltac_term:(G)) | idtac "SSR	pp.3	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _)); elpi z_report "pp.3" "122" ltac_term:(G)) | idtac "SSR	pp.3	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(false); elpi z_report "pp.3" "123" ltac_term:(G)) | idtac "SSR	pp.3	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(false); elpi z_report "pp.3" "124" ltac_term:(G)) | idtac "SSR	pp.3	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false X _ _ _ _ _ _); elpi z_report "pp.3" "125" ltac_term:(G)) | idtac "SSR	pp.3	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false X _ _ _ _ _ _) _); elpi z_report "pp.3" "126" ltac_term:(G)) | idtac "SSR	pp.3	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _)); elpi z_report "pp.3" "127" ltac_term:(G)) | idtac "SSR	pp.3	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _) = _); elpi z_report "pp.3" "128" ltac_term:(G)) | idtac "SSR	pp.3	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false _ X _ _ _ _ _); elpi z_report "pp.3" "129" ltac_term:(G)) | idtac "SSR	pp.3	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ X _ _ _ _ _) _); elpi z_report "pp.3" "130" ltac_term:(G)) | idtac "SSR	pp.3	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _)); elpi z_report "pp.3" "131" ltac_term:(G)) | idtac "SSR	pp.3	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(false); elpi z_report "pp.3" "132" ltac_term:(G)) | idtac "SSR	pp.3	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(false); elpi z_report "pp.3" "133" ltac_term:(G)) | idtac "SSR	pp.3	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false _ X _ _ _ _ _); elpi z_report "pp.3" "134" ltac_term:(G)) | idtac "SSR	pp.3	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ X _ _ _ _ _) _); elpi z_report "pp.3" "135" ltac_term:(G)) | idtac "SSR	pp.3	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _)); elpi z_report "pp.3" "136" ltac_term:(G)) | idtac "SSR	pp.3	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _) = _); elpi z_report "pp.3" "137" ltac_term:(G)) | idtac "SSR	pp.3	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false _ _ X _ _ _ _); elpi z_report "pp.3" "138" ltac_term:(G)) | idtac "SSR	pp.3	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ _ X _ _ _ _) _); elpi z_report "pp.3" "139" ltac_term:(G)) | idtac "SSR	pp.3	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _)); elpi z_report "pp.3" "140" ltac_term:(G)) | idtac "SSR	pp.3	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(false); elpi z_report "pp.3" "141" ltac_term:(G)) | idtac "SSR	pp.3	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(false); elpi z_report "pp.3" "142" ltac_term:(G)) | idtac "SSR	pp.3	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false _ _ X _ _ _ _); elpi z_report "pp.3" "143" ltac_term:(G)) | idtac "SSR	pp.3	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ _ X _ _ _ _) _); elpi z_report "pp.3" "144" ltac_term:(G)) | idtac "SSR	pp.3	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _)); elpi z_report "pp.3" "145" ltac_term:(G)) | idtac "SSR	pp.3	145	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _) = _); elpi z_report "pp.3" "146" ltac_term:(G)) | idtac "SSR	pp.3	146	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false _ _ _ X _ _ _); elpi z_report "pp.3" "147" ltac_term:(G)) | idtac "SSR	pp.3	147	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ _ _ X _ _ _) _); elpi z_report "pp.3" "148" ltac_term:(G)) | idtac "SSR	pp.3	148	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _)); elpi z_report "pp.3" "149" ltac_term:(G)) | idtac "SSR	pp.3	149	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(false); elpi z_report "pp.3" "150" ltac_term:(G)) | idtac "SSR	pp.3	150	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(false); elpi z_report "pp.3" "151" ltac_term:(G)) | idtac "SSR	pp.3	151	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false _ _ _ X _ _ _); elpi z_report "pp.3" "152" ltac_term:(G)) | idtac "SSR	pp.3	152	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ _ _ X _ _ _) _); elpi z_report "pp.3" "153" ltac_term:(G)) | idtac "SSR	pp.3	153	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _)); elpi z_report "pp.3" "154" ltac_term:(G)) | idtac "SSR	pp.3	154	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _) = _); elpi z_report "pp.3" "155" ltac_term:(G)) | idtac "SSR	pp.3	155	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false _ _ _ _ X _ _); elpi z_report "pp.3" "156" ltac_term:(G)) | idtac "SSR	pp.3	156	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ _ _ _ X _ _) _); elpi z_report "pp.3" "157" ltac_term:(G)) | idtac "SSR	pp.3	157	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _)); elpi z_report "pp.3" "158" ltac_term:(G)) | idtac "SSR	pp.3	158	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(true); elpi z_report "pp.3" "159" ltac_term:(G)) | idtac "SSR	pp.3	159	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(true); elpi z_report "pp.3" "160" ltac_term:(G)) | idtac "SSR	pp.3	160	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false _ _ _ _ X _ _); elpi z_report "pp.3" "161" ltac_term:(G)) | idtac "SSR	pp.3	161	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ _ _ _ X _ _) _); elpi z_report "pp.3" "162" ltac_term:(G)) | idtac "SSR	pp.3	162	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _)); elpi z_report "pp.3" "163" ltac_term:(G)) | idtac "SSR	pp.3	163	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _) = _); elpi z_report "pp.3" "164" ltac_term:(G)) | idtac "SSR	pp.3	164	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false _ _ _ _ _ X _); elpi z_report "pp.3" "165" ltac_term:(G)) | idtac "SSR	pp.3	165	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ _ _ _ _ X _) _); elpi z_report "pp.3" "166" ltac_term:(G)) | idtac "SSR	pp.3	166	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _)); elpi z_report "pp.3" "167" ltac_term:(G)) | idtac "SSR	pp.3	167	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {11}(false); elpi z_report "pp.3" "168" ltac_term:(G)) | idtac "SSR	pp.3	168	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {11}(false); elpi z_report "pp.3" "169" ltac_term:(G)) | idtac "SSR	pp.3	169	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false _ _ _ _ _ X _); elpi z_report "pp.3" "170" ltac_term:(G)) | idtac "SSR	pp.3	170	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ _ _ _ _ X _) _); elpi z_report "pp.3" "171" ltac_term:(G)) | idtac "SSR	pp.3	171	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _)); elpi z_report "pp.3" "172" ltac_term:(G)) | idtac "SSR	pp.3	172	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _) = _); elpi z_report "pp.3" "173" ltac_term:(G)) | idtac "SSR	pp.3	173	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false _ _ _ _ _ _ X); elpi z_report "pp.3" "174" ltac_term:(G)) | idtac "SSR	pp.3	174	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ _ _ _ _ _ X) _); elpi z_report "pp.3" "175" ltac_term:(G)) | idtac "SSR	pp.3	175	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _)); elpi z_report "pp.3" "176" ltac_term:(G)) | idtac "SSR	pp.3	176	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {12}(false); elpi z_report "pp.3" "177" ltac_term:(G)) | idtac "SSR	pp.3	177	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {12}(false); elpi z_report "pp.3" "178" ltac_term:(G)) | idtac "SSR	pp.3	178	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false _ _ _ _ _ _ X); elpi z_report "pp.3" "179" ltac_term:(G)) | idtac "SSR	pp.3	179	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ _ _ _ _ _ X) _); elpi z_report "pp.3" "180" ltac_term:(G)) | idtac "SSR	pp.3	180	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _)); elpi z_report "pp.3" "181" ltac_term:(G)) | idtac "SSR	pp.3	181	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ "" in X in X = _); elpi z_report "pp.3" "182" ltac_term:(G)) | idtac "SSR	pp.3	182	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ X) = _); elpi z_report "pp.3" "183" ltac_term:(G)) | idtac "SSR	pp.3	183	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ "" in X in String _ X = _); elpi z_report "pp.3" "184" ltac_term:(G)) | idtac "SSR	pp.3	184	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in String _ (String _ X) = _); elpi z_report "pp.3" "185" ltac_term:(G)) | idtac "SSR	pp.3	185	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ X)); elpi z_report "pp.3" "186" ltac_term:(G)) | idtac "SSR	pp.3	186	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ "" in X in String _ X); elpi z_report "pp.3" "187" ltac_term:(G)) | idtac "SSR	pp.3	187	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ _ _ _ _ _ _) X); elpi z_report "pp.3" "188" ltac_term:(G)) | idtac "SSR	pp.3	188	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}("b"%string); elpi z_report "pp.3" "189" ltac_term:(G)) | idtac "SSR	pp.3	189	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String _ ""); elpi z_report "pp.3" "190" ltac_term:(G)) | idtac "SSR	pp.3	190	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ X)); elpi z_report "pp.3" "191" ltac_term:(G)) | idtac "SSR	pp.3	191	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String _ "" as X in String _ X); elpi z_report "pp.3" "192" ltac_term:(G)) | idtac "SSR	pp.3	192	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String _ "" in X in String _ X); elpi z_report "pp.3" "193" ltac_term:(G)) | idtac "SSR	pp.3	193	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ _ _ _ _ _ _) X); elpi z_report "pp.3" "194" ltac_term:(G)) | idtac "SSR	pp.3	194	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(String _ _ as X in String _ (String _ X)); elpi z_report "pp.3" "195" ltac_term:(G)) | idtac "SSR	pp.3	195	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(String); elpi z_report "pp.3" "196" ltac_term:(G)) | idtac "SSR	pp.3	196	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(String); elpi z_report "pp.3" "197" ltac_term:(G)) | idtac "SSR	pp.3	197	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ in X in X = _); elpi z_report "pp.3" "198" ltac_term:(G)) | idtac "SSR	pp.3	198	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ in X in String _ X = _); elpi z_report "pp.3" "199" ltac_term:(G)) | idtac "SSR	pp.3	199	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String X _)) = _); elpi z_report "pp.3" "200" ltac_term:(G)) | idtac "SSR	pp.3	200	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in String _ (String _ (String X _)) = _); elpi z_report "pp.3" "201" ltac_term:(G)) | idtac "SSR	pp.3	201	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ in X in String _ X); elpi z_report "pp.3" "202" ltac_term:(G)) | idtac "SSR	pp.3	202	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in String _ (String _ X)); elpi z_report "pp.3" "203" ltac_term:(G)) | idtac "SSR	pp.3	203	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii false _ _ _ _ _ _ _) X); elpi z_report "pp.3" "204" ltac_term:(G)) | idtac "SSR	pp.3	204	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ true _ _ _ _ _ _); elpi z_report "pp.3" "205" ltac_term:(G)) | idtac "SSR	pp.3	205	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String X ""); elpi z_report "pp.3" "206" ltac_term:(G)) | idtac "SSR	pp.3	206	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ true _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "207" ltac_term:(G)) | idtac "SSR	pp.3	207	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ true _ _ _ _ _ _ in X in String _ X); elpi z_report "pp.3" "208" ltac_term:(G)) | idtac "SSR	pp.3	208	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String X "")); elpi z_report "pp.3" "209" ltac_term:(G)) | idtac "SSR	pp.3	209	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ _ _ _ _ _ _ _ in X in String _ (String _ X)); elpi z_report "pp.3" "210" ltac_term:(G)) | idtac "SSR	pp.3	210	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String X _))); elpi z_report "pp.3" "211" ltac_term:(G)) | idtac "SSR	pp.3	211	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii false _ _ _ _ _ _ _) X); elpi z_report "pp.3" "212" ltac_term:(G)) | idtac "SSR	pp.3	212	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ true _ _ _ _ _ _ as X in String _ (String X _)); elpi z_report "pp.3" "213" ltac_term:(G)) | idtac "SSR	pp.3	213	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii _ _ _ _ _ _ _ _ as X in String _ (String _ (String X _))); elpi z_report "pp.3" "214" ltac_term:(G)) | idtac "SSR	pp.3	214	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Ascii.Ascii false true false false false true true false); elpi z_report "pp.3" "215" ltac_term:(G)) | idtac "SSR	pp.3	215	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Ascii.Ascii); elpi z_report "pp.3" "216" ltac_term:(G)) | idtac "SSR	pp.3	216	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Ascii.Ascii); elpi z_report "pp.3" "217" ltac_term:(G)) | idtac "SSR	pp.3	217	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _)) = _); elpi z_report "pp.3" "218" ltac_term:(G)) | idtac "SSR	pp.3	218	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {13}(false); elpi z_report "pp.3" "219" ltac_term:(G)) | idtac "SSR	pp.3	219	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {13}(false); elpi z_report "pp.3" "220" ltac_term:(G)) | idtac "SSR	pp.3	220	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii X true _ _ _ _ _ _); elpi z_report "pp.3" "221" ltac_term:(G)) | idtac "SSR	pp.3	221	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii X true _ _ _ _ _ _) _); elpi z_report "pp.3" "222" ltac_term:(G)) | idtac "SSR	pp.3	222	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii X true _ _ _ _ _ _) _)); elpi z_report "pp.3" "223" ltac_term:(G)) | idtac "SSR	pp.3	223	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _))); elpi z_report "pp.3" "224" ltac_term:(G)) | idtac "SSR	pp.3	224	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _)) = _); elpi z_report "pp.3" "225" ltac_term:(G)) | idtac "SSR	pp.3	225	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(true); elpi z_report "pp.3" "226" ltac_term:(G)) | idtac "SSR	pp.3	226	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(true); elpi z_report "pp.3" "227" ltac_term:(G)) | idtac "SSR	pp.3	227	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii false X _ _ _ _ true _); elpi z_report "pp.3" "228" ltac_term:(G)) | idtac "SSR	pp.3	228	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ X _ _ _ _ _ _) ""); elpi z_report "pp.3" "229" ltac_term:(G)) | idtac "SSR	pp.3	229	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ X _ _ _ _ true _) _)); elpi z_report "pp.3" "230" ltac_term:(G)) | idtac "SSR	pp.3	230	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _))); elpi z_report "pp.3" "231" ltac_term:(G)) | idtac "SSR	pp.3	231	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _)) = _); elpi z_report "pp.3" "232" ltac_term:(G)) | idtac "SSR	pp.3	232	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {14}(false); elpi z_report "pp.3" "233" ltac_term:(G)) | idtac "SSR	pp.3	233	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {14}(false); elpi z_report "pp.3" "234" ltac_term:(G)) | idtac "SSR	pp.3	234	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ true X _ _ _ _ _); elpi z_report "pp.3" "235" ltac_term:(G)) | idtac "SSR	pp.3	235	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ true X _ _ _ _ _) _); elpi z_report "pp.3" "236" ltac_term:(G)) | idtac "SSR	pp.3	236	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ true X _ _ _ _ _) _)); elpi z_report "pp.3" "237" ltac_term:(G)) | idtac "SSR	pp.3	237	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _))); elpi z_report "pp.3" "238" ltac_term:(G)) | idtac "SSR	pp.3	238	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _)) = _); elpi z_report "pp.3" "239" ltac_term:(G)) | idtac "SSR	pp.3	239	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {15}(false); elpi z_report "pp.3" "240" ltac_term:(G)) | idtac "SSR	pp.3	240	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {15}(false); elpi z_report "pp.3" "241" ltac_term:(G)) | idtac "SSR	pp.3	241	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ true _ X _ _ _ _); elpi z_report "pp.3" "242" ltac_term:(G)) | idtac "SSR	pp.3	242	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ true _ X _ _ _ _) _); elpi z_report "pp.3" "243" ltac_term:(G)) | idtac "SSR	pp.3	243	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ true _ X _ _ _ _) _)); elpi z_report "pp.3" "244" ltac_term:(G)) | idtac "SSR	pp.3	244	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _))); elpi z_report "pp.3" "245" ltac_term:(G)) | idtac "SSR	pp.3	245	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _)) = _); elpi z_report "pp.3" "246" ltac_term:(G)) | idtac "SSR	pp.3	246	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {16}(false); elpi z_report "pp.3" "247" ltac_term:(G)) | idtac "SSR	pp.3	247	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {16}(false); elpi z_report "pp.3" "248" ltac_term:(G)) | idtac "SSR	pp.3	248	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ true _ _ X _ _ _); elpi z_report "pp.3" "249" ltac_term:(G)) | idtac "SSR	pp.3	249	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ true _ _ X _ _ _) _); elpi z_report "pp.3" "250" ltac_term:(G)) | idtac "SSR	pp.3	250	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ true _ _ X _ _ _) _)); elpi z_report "pp.3" "251" ltac_term:(G)) | idtac "SSR	pp.3	251	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _))); elpi z_report "pp.3" "252" ltac_term:(G)) | idtac "SSR	pp.3	252	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _)) = _); elpi z_report "pp.3" "253" ltac_term:(G)) | idtac "SSR	pp.3	253	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(true); elpi z_report "pp.3" "254" ltac_term:(G)) | idtac "SSR	pp.3	254	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(true); elpi z_report "pp.3" "255" ltac_term:(G)) | idtac "SSR	pp.3	255	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ true _ _ _ X _ _); elpi z_report "pp.3" "256" ltac_term:(G)) | idtac "SSR	pp.3	256	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ true _ _ _ X _ _) _); elpi z_report "pp.3" "257" ltac_term:(G)) | idtac "SSR	pp.3	257	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ true _ _ _ X _ _) _)); elpi z_report "pp.3" "258" ltac_term:(G)) | idtac "SSR	pp.3	258	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _))); elpi z_report "pp.3" "259" ltac_term:(G)) | idtac "SSR	pp.3	259	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _)) = _); elpi z_report "pp.3" "260" ltac_term:(G)) | idtac "SSR	pp.3	260	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(true); elpi z_report "pp.3" "261" ltac_term:(G)) | idtac "SSR	pp.3	261	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(true); elpi z_report "pp.3" "262" ltac_term:(G)) | idtac "SSR	pp.3	262	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ true _ _ _ _ X _); elpi z_report "pp.3" "263" ltac_term:(G)) | idtac "SSR	pp.3	263	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ true _ _ _ _ X _) _); elpi z_report "pp.3" "264" ltac_term:(G)) | idtac "SSR	pp.3	264	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ true _ _ _ _ X _) _)); elpi z_report "pp.3" "265" ltac_term:(G)) | idtac "SSR	pp.3	265	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _))); elpi z_report "pp.3" "266" ltac_term:(G)) | idtac "SSR	pp.3	266	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _)) = _); elpi z_report "pp.3" "267" ltac_term:(G)) | idtac "SSR	pp.3	267	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {17}(false); elpi z_report "pp.3" "268" ltac_term:(G)) | idtac "SSR	pp.3	268	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {17}(false); elpi z_report "pp.3" "269" ltac_term:(G)) | idtac "SSR	pp.3	269	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in Ascii.Ascii _ true _ _ _ _ _ X); elpi z_report "pp.3" "270" ltac_term:(G)) | idtac "SSR	pp.3	270	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ true _ _ _ _ _ X) _); elpi z_report "pp.3" "271" ltac_term:(G)) | idtac "SSR	pp.3	271	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String (Ascii.Ascii _ true _ _ _ _ _ X) _)); elpi z_report "pp.3" "272" ltac_term:(G)) | idtac "SSR	pp.3	272	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _))); elpi z_report "pp.3" "273" ltac_term:(G)) | idtac "SSR	pp.3	273	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String _ X)) = _); elpi z_report "pp.3" "274" ltac_term:(G)) | idtac "SSR	pp.3	274	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(""%string); elpi z_report "pp.3" "275" ltac_term:(G)) | idtac "SSR	pp.3	275	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(""%string); elpi z_report "pp.3" "276" ltac_term:(G)) | idtac "SSR	pp.3	276	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii _ true _ _ _ _ _ _) X); elpi z_report "pp.3" "277" ltac_term:(G)) | idtac "SSR	pp.3	277	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String _ (String _ (String _ X))); elpi z_report "pp.3" "278" ltac_term:(G)) | idtac "SSR	pp.3	278	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in String (Ascii.Ascii false _ _ _ _ _ _ _) (String _ X)); elpi z_report "pp.3" "279" ltac_term:(G)) | idtac "SSR	pp.3	279	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.3" "280" ltac_term:(G)) | idtac "SSR	pp.3	280	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in _ = X); elpi z_report "pp.3" "281" ltac_term:(G)) | idtac "SSR	pp.3	281	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String (Ascii.Ascii true _ _ _ _ _ _ _) _); elpi z_report "pp.3" "282" ltac_term:(G)) | idtac "SSR	pp.3	282	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}("a b"%string); elpi z_report "pp.3" "283" ltac_term:(G)) | idtac "SSR	pp.3	283	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String (Ascii.Ascii true _ _ _ _ _ _ _) _); elpi z_report "pp.3" "284" ltac_term:(G)) | idtac "SSR	pp.3	284	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(String); elpi z_report "pp.3" "285" ltac_term:(G)) | idtac "SSR	pp.3	285	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(String); elpi z_report "pp.3" "286" ltac_term:(G)) | idtac "SSR	pp.3	286	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in _ = X); elpi z_report "pp.3" "287" ltac_term:(G)) | idtac "SSR	pp.3	287	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String X _); elpi z_report "pp.3" "288" ltac_term:(G)) | idtac "SSR	pp.3	288	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in _ = String X _); elpi z_report "pp.3" "289" ltac_term:(G)) | idtac "SSR	pp.3	289	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii true _ _ _ _ _ _ _); elpi z_report "pp.3" "290" ltac_term:(G)) | idtac "SSR	pp.3	290	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii true _ _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "291" ltac_term:(G)) | idtac "SSR	pp.3	291	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String X (String (Ascii.Ascii _ false _ _ _ _ _ _) _)); elpi z_report "pp.3" "292" ltac_term:(G)) | idtac "SSR	pp.3	292	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii true _ _ _ _ _ _ _); elpi z_report "pp.3" "293" ltac_term:(G)) | idtac "SSR	pp.3	293	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii true _ _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "294" ltac_term:(G)) | idtac "SSR	pp.3	294	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String X (String (Ascii.Ascii _ false _ _ _ _ _ _) _)); elpi z_report "pp.3" "295" ltac_term:(G)) | idtac "SSR	pp.3	295	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii true false false false false true true false); elpi z_report "pp.3" "296" ltac_term:(G)) | idtac "SSR	pp.3	296	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Ascii.Ascii); elpi z_report "pp.3" "297" ltac_term:(G)) | idtac "SSR	pp.3	297	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Ascii.Ascii); elpi z_report "pp.3" "298" ltac_term:(G)) | idtac "SSR	pp.3	298	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii X _ _ _ _ _ _ _) _); elpi z_report "pp.3" "299" ltac_term:(G)) | idtac "SSR	pp.3	299	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii X false _ _ _ _ true _); elpi z_report "pp.3" "300" ltac_term:(G)) | idtac "SSR	pp.3	300	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii X false _ _ _ _ true _) _); elpi z_report "pp.3" "301" ltac_term:(G)) | idtac "SSR	pp.3	301	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(true); elpi z_report "pp.3" "302" ltac_term:(G)) | idtac "SSR	pp.3	302	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(true); elpi z_report "pp.3" "303" ltac_term:(G)) | idtac "SSR	pp.3	303	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii X false _ _ _ _ true _); elpi z_report "pp.3" "304" ltac_term:(G)) | idtac "SSR	pp.3	304	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii X false _ _ _ _ true _) _); elpi z_report "pp.3" "305" ltac_term:(G)) | idtac "SSR	pp.3	305	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii _ X _ _ _ _ _ _) _); elpi z_report "pp.3" "306" ltac_term:(G)) | idtac "SSR	pp.3	306	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii true X _ _ _ _ _ _); elpi z_report "pp.3" "307" ltac_term:(G)) | idtac "SSR	pp.3	307	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true X _ _ _ _ _ _) _); elpi z_report "pp.3" "308" ltac_term:(G)) | idtac "SSR	pp.3	308	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {18}(false); elpi z_report "pp.3" "309" ltac_term:(G)) | idtac "SSR	pp.3	309	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {18}(false); elpi z_report "pp.3" "310" ltac_term:(G)) | idtac "SSR	pp.3	310	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii true X _ _ _ _ _ _); elpi z_report "pp.3" "311" ltac_term:(G)) | idtac "SSR	pp.3	311	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true X _ _ _ _ _ _) _); elpi z_report "pp.3" "312" ltac_term:(G)) | idtac "SSR	pp.3	312	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii _ _ X _ _ _ _ _) _); elpi z_report "pp.3" "313" ltac_term:(G)) | idtac "SSR	pp.3	313	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii true _ X _ _ _ _ _); elpi z_report "pp.3" "314" ltac_term:(G)) | idtac "SSR	pp.3	314	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ X _ _ _ _ _) _); elpi z_report "pp.3" "315" ltac_term:(G)) | idtac "SSR	pp.3	315	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {19}(false); elpi z_report "pp.3" "316" ltac_term:(G)) | idtac "SSR	pp.3	316	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {19}(false); elpi z_report "pp.3" "317" ltac_term:(G)) | idtac "SSR	pp.3	317	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii true _ X _ _ _ _ _); elpi z_report "pp.3" "318" ltac_term:(G)) | idtac "SSR	pp.3	318	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ X _ _ _ _ _) _); elpi z_report "pp.3" "319" ltac_term:(G)) | idtac "SSR	pp.3	319	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii _ _ _ X _ _ _ _) _); elpi z_report "pp.3" "320" ltac_term:(G)) | idtac "SSR	pp.3	320	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii true _ _ X _ _ _ _); elpi z_report "pp.3" "321" ltac_term:(G)) | idtac "SSR	pp.3	321	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ X _ _ _ _) _); elpi z_report "pp.3" "322" ltac_term:(G)) | idtac "SSR	pp.3	322	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {20}(false); elpi z_report "pp.3" "323" ltac_term:(G)) | idtac "SSR	pp.3	323	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {20}(false); elpi z_report "pp.3" "324" ltac_term:(G)) | idtac "SSR	pp.3	324	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii true _ _ X _ _ _ _); elpi z_report "pp.3" "325" ltac_term:(G)) | idtac "SSR	pp.3	325	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ X _ _ _ _) _); elpi z_report "pp.3" "326" ltac_term:(G)) | idtac "SSR	pp.3	326	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii _ _ _ _ X _ _ _) _); elpi z_report "pp.3" "327" ltac_term:(G)) | idtac "SSR	pp.3	327	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii true _ _ _ X _ _ _); elpi z_report "pp.3" "328" ltac_term:(G)) | idtac "SSR	pp.3	328	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ _ X _ _ _) _); elpi z_report "pp.3" "329" ltac_term:(G)) | idtac "SSR	pp.3	329	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {21}(false); elpi z_report "pp.3" "330" ltac_term:(G)) | idtac "SSR	pp.3	330	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {21}(false); elpi z_report "pp.3" "331" ltac_term:(G)) | idtac "SSR	pp.3	331	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii true _ _ _ X _ _ _); elpi z_report "pp.3" "332" ltac_term:(G)) | idtac "SSR	pp.3	332	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ _ X _ _ _) _); elpi z_report "pp.3" "333" ltac_term:(G)) | idtac "SSR	pp.3	333	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii _ _ _ _ _ X _ _) _); elpi z_report "pp.3" "334" ltac_term:(G)) | idtac "SSR	pp.3	334	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii true _ _ _ _ X _ _); elpi z_report "pp.3" "335" ltac_term:(G)) | idtac "SSR	pp.3	335	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ _ _ X _ _) _); elpi z_report "pp.3" "336" ltac_term:(G)) | idtac "SSR	pp.3	336	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(true); elpi z_report "pp.3" "337" ltac_term:(G)) | idtac "SSR	pp.3	337	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(true); elpi z_report "pp.3" "338" ltac_term:(G)) | idtac "SSR	pp.3	338	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii true _ _ _ _ X _ _); elpi z_report "pp.3" "339" ltac_term:(G)) | idtac "SSR	pp.3	339	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ _ _ X _ _) _); elpi z_report "pp.3" "340" ltac_term:(G)) | idtac "SSR	pp.3	340	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii _ _ _ _ _ _ X _) _); elpi z_report "pp.3" "341" ltac_term:(G)) | idtac "SSR	pp.3	341	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii true _ _ _ _ _ X _); elpi z_report "pp.3" "342" ltac_term:(G)) | idtac "SSR	pp.3	342	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ _ _ _ X _) _); elpi z_report "pp.3" "343" ltac_term:(G)) | idtac "SSR	pp.3	343	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(true); elpi z_report "pp.3" "344" ltac_term:(G)) | idtac "SSR	pp.3	344	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(true); elpi z_report "pp.3" "345" ltac_term:(G)) | idtac "SSR	pp.3	345	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii true _ _ _ _ _ X _); elpi z_report "pp.3" "346" ltac_term:(G)) | idtac "SSR	pp.3	346	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ _ _ _ X _) _); elpi z_report "pp.3" "347" ltac_term:(G)) | idtac "SSR	pp.3	347	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String (Ascii.Ascii _ _ _ _ _ _ _ X) _); elpi z_report "pp.3" "348" ltac_term:(G)) | idtac "SSR	pp.3	348	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii true _ _ _ _ _ _ X); elpi z_report "pp.3" "349" ltac_term:(G)) | idtac "SSR	pp.3	349	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ _ _ _ _ X) _); elpi z_report "pp.3" "350" ltac_term:(G)) | idtac "SSR	pp.3	350	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {22}(false); elpi z_report "pp.3" "351" ltac_term:(G)) | idtac "SSR	pp.3	351	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {22}(false); elpi z_report "pp.3" "352" ltac_term:(G)) | idtac "SSR	pp.3	352	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii true _ _ _ _ _ _ X); elpi z_report "pp.3" "353" ltac_term:(G)) | idtac "SSR	pp.3	353	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ _ _ _ _ X) _); elpi z_report "pp.3" "354" ltac_term:(G)) | idtac "SSR	pp.3	354	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ X); elpi z_report "pp.3" "355" ltac_term:(G)) | idtac "SSR	pp.3	355	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in _ = String _ X); elpi z_report "pp.3" "356" ltac_term:(G)) | idtac "SSR	pp.3	356	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String (Ascii.Ascii false _ _ _ _ _ _ _) _ in X in _ = X); elpi z_report "pp.3" "357" ltac_term:(G)) | idtac "SSR	pp.3	357	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String (Ascii.Ascii _ _ _ _ _ _ false _) _); elpi z_report "pp.3" "358" ltac_term:(G)) | idtac "SSR	pp.3	358	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "359" ltac_term:(G)) | idtac "SSR	pp.3	359	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "360" ltac_term:(G)) | idtac "SSR	pp.3	360	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(" b"%string); elpi z_report "pp.3" "361" ltac_term:(G)) | idtac "SSR	pp.3	361	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String (Ascii.Ascii _ _ _ _ _ _ false _) _); elpi z_report "pp.3" "362" ltac_term:(G)) | idtac "SSR	pp.3	362	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "363" ltac_term:(G)) | idtac "SSR	pp.3	363	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String _ _ as X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "364" ltac_term:(G)) | idtac "SSR	pp.3	364	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(String); elpi z_report "pp.3" "365" ltac_term:(G)) | idtac "SSR	pp.3	365	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(String); elpi z_report "pp.3" "366" ltac_term:(G)) | idtac "SSR	pp.3	366	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii false _ _ _ _ _ _ _ in X in _ = X); elpi z_report "pp.3" "367" ltac_term:(G)) | idtac "SSR	pp.3	367	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in _ = String _ X); elpi z_report "pp.3" "368" ltac_term:(G)) | idtac "SSR	pp.3	368	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String X _)); elpi z_report "pp.3" "369" ltac_term:(G)) | idtac "SSR	pp.3	369	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in _ = String _ (String X _)); elpi z_report "pp.3" "370" ltac_term:(G)) | idtac "SSR	pp.3	370	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ false _); elpi z_report "pp.3" "371" ltac_term:(G)) | idtac "SSR	pp.3	371	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String X (String _ "")); elpi z_report "pp.3" "372" ltac_term:(G)) | idtac "SSR	pp.3	372	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ false _ as X in String X _); elpi z_report "pp.3" "373" ltac_term:(G)) | idtac "SSR	pp.3	373	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "374" ltac_term:(G)) | idtac "SSR	pp.3	374	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ _ _ _ _ _) (String X _)); elpi z_report "pp.3" "375" ltac_term:(G)) | idtac "SSR	pp.3	375	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ false _ _ _ _ _ _ as X in String _ (String X _)); elpi z_report "pp.3" "376" ltac_term:(G)) | idtac "SSR	pp.3	376	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ _ _ _ _ _ false _); elpi z_report "pp.3" "377" ltac_term:(G)) | idtac "SSR	pp.3	377	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String X (String _ "")); elpi z_report "pp.3" "378" ltac_term:(G)) | idtac "SSR	pp.3	378	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ _ _ _ _ _ false _ as X in String X _); elpi z_report "pp.3" "379" ltac_term:(G)) | idtac "SSR	pp.3	379	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "380" ltac_term:(G)) | idtac "SSR	pp.3	380	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ _ _ _ _ _) (String X _)); elpi z_report "pp.3" "381" ltac_term:(G)) | idtac "SSR	pp.3	381	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ false _ _ _ _ _ _ as X in String _ (String X _)); elpi z_report "pp.3" "382" ltac_term:(G)) | idtac "SSR	pp.3	382	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii false false false false false true false false); elpi z_report "pp.3" "383" ltac_term:(G)) | idtac "SSR	pp.3	383	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Ascii.Ascii); elpi z_report "pp.3" "384" ltac_term:(G)) | idtac "SSR	pp.3	384	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Ascii.Ascii); elpi z_report "pp.3" "385" ltac_term:(G)) | idtac "SSR	pp.3	385	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _)); elpi z_report "pp.3" "386" ltac_term:(G)) | idtac "SSR	pp.3	386	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii X _ _ _ _ _ false _); elpi z_report "pp.3" "387" ltac_term:(G)) | idtac "SSR	pp.3	387	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii X _ _ _ _ _ false _) _); elpi z_report "pp.3" "388" ltac_term:(G)) | idtac "SSR	pp.3	388	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii X false _ _ _ _ _ _) _)); elpi z_report "pp.3" "389" ltac_term:(G)) | idtac "SSR	pp.3	389	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {23}(false); elpi z_report "pp.3" "390" ltac_term:(G)) | idtac "SSR	pp.3	390	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {23}(false); elpi z_report "pp.3" "391" ltac_term:(G)) | idtac "SSR	pp.3	391	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii X _ _ _ _ _ false _); elpi z_report "pp.3" "392" ltac_term:(G)) | idtac "SSR	pp.3	392	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii X _ _ _ _ _ false _) _); elpi z_report "pp.3" "393" ltac_term:(G)) | idtac "SSR	pp.3	393	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii X false _ _ _ _ _ _) _)); elpi z_report "pp.3" "394" ltac_term:(G)) | idtac "SSR	pp.3	394	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _)); elpi z_report "pp.3" "395" ltac_term:(G)) | idtac "SSR	pp.3	395	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ X _ _ _ _ false _); elpi z_report "pp.3" "396" ltac_term:(G)) | idtac "SSR	pp.3	396	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ X _ _ _ _ false _) _); elpi z_report "pp.3" "397" ltac_term:(G)) | idtac "SSR	pp.3	397	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ X _ _ _ _ false _) _)); elpi z_report "pp.3" "398" ltac_term:(G)) | idtac "SSR	pp.3	398	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {24}(false); elpi z_report "pp.3" "399" ltac_term:(G)) | idtac "SSR	pp.3	399	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {24}(false); elpi z_report "pp.3" "400" ltac_term:(G)) | idtac "SSR	pp.3	400	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ X _ _ _ _ false _); elpi z_report "pp.3" "401" ltac_term:(G)) | idtac "SSR	pp.3	401	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ X _ _ _ _ false _) _); elpi z_report "pp.3" "402" ltac_term:(G)) | idtac "SSR	pp.3	402	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ X _ _ _ _ false _) _)); elpi z_report "pp.3" "403" ltac_term:(G)) | idtac "SSR	pp.3	403	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _)); elpi z_report "pp.3" "404" ltac_term:(G)) | idtac "SSR	pp.3	404	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ X _ _ _ false _); elpi z_report "pp.3" "405" ltac_term:(G)) | idtac "SSR	pp.3	405	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ X _ _ _ false _) _); elpi z_report "pp.3" "406" ltac_term:(G)) | idtac "SSR	pp.3	406	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ false X _ _ _ _ _) _)); elpi z_report "pp.3" "407" ltac_term:(G)) | idtac "SSR	pp.3	407	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {25}(false); elpi z_report "pp.3" "408" ltac_term:(G)) | idtac "SSR	pp.3	408	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {25}(false); elpi z_report "pp.3" "409" ltac_term:(G)) | idtac "SSR	pp.3	409	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ _ X _ _ _ false _); elpi z_report "pp.3" "410" ltac_term:(G)) | idtac "SSR	pp.3	410	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ _ X _ _ _ false _) _); elpi z_report "pp.3" "411" ltac_term:(G)) | idtac "SSR	pp.3	411	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ false X _ _ _ _ _) _)); elpi z_report "pp.3" "412" ltac_term:(G)) | idtac "SSR	pp.3	412	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _)); elpi z_report "pp.3" "413" ltac_term:(G)) | idtac "SSR	pp.3	413	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ X _ _ false _); elpi z_report "pp.3" "414" ltac_term:(G)) | idtac "SSR	pp.3	414	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ X _ _ false _) _); elpi z_report "pp.3" "415" ltac_term:(G)) | idtac "SSR	pp.3	415	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ false _ X _ _ _ _) _)); elpi z_report "pp.3" "416" ltac_term:(G)) | idtac "SSR	pp.3	416	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {26}(false); elpi z_report "pp.3" "417" ltac_term:(G)) | idtac "SSR	pp.3	417	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {26}(false); elpi z_report "pp.3" "418" ltac_term:(G)) | idtac "SSR	pp.3	418	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ _ _ X _ _ false _); elpi z_report "pp.3" "419" ltac_term:(G)) | idtac "SSR	pp.3	419	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ _ _ X _ _ false _) _); elpi z_report "pp.3" "420" ltac_term:(G)) | idtac "SSR	pp.3	420	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ false _ X _ _ _ _) _)); elpi z_report "pp.3" "421" ltac_term:(G)) | idtac "SSR	pp.3	421	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _)); elpi z_report "pp.3" "422" ltac_term:(G)) | idtac "SSR	pp.3	422	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ _ X _ false _); elpi z_report "pp.3" "423" ltac_term:(G)) | idtac "SSR	pp.3	423	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ X _ false _) _); elpi z_report "pp.3" "424" ltac_term:(G)) | idtac "SSR	pp.3	424	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ false _ _ X _ _ _) _)); elpi z_report "pp.3" "425" ltac_term:(G)) | idtac "SSR	pp.3	425	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {27}(false); elpi z_report "pp.3" "426" ltac_term:(G)) | idtac "SSR	pp.3	426	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {27}(false); elpi z_report "pp.3" "427" ltac_term:(G)) | idtac "SSR	pp.3	427	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ _ _ _ X _ false _); elpi z_report "pp.3" "428" ltac_term:(G)) | idtac "SSR	pp.3	428	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ _ _ _ X _ false _) _); elpi z_report "pp.3" "429" ltac_term:(G)) | idtac "SSR	pp.3	429	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ false _ _ X _ _ _) _)); elpi z_report "pp.3" "430" ltac_term:(G)) | idtac "SSR	pp.3	430	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _)); elpi z_report "pp.3" "431" ltac_term:(G)) | idtac "SSR	pp.3	431	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ _ _ X false _); elpi z_report "pp.3" "432" ltac_term:(G)) | idtac "SSR	pp.3	432	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ X false _) _); elpi z_report "pp.3" "433" ltac_term:(G)) | idtac "SSR	pp.3	433	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ false _ _ _ X _ _) _)); elpi z_report "pp.3" "434" ltac_term:(G)) | idtac "SSR	pp.3	434	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {11}(true); elpi z_report "pp.3" "435" ltac_term:(G)) | idtac "SSR	pp.3	435	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {11}(true); elpi z_report "pp.3" "436" ltac_term:(G)) | idtac "SSR	pp.3	436	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ _ _ _ _ X false _); elpi z_report "pp.3" "437" ltac_term:(G)) | idtac "SSR	pp.3	437	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ _ _ _ _ X false _) _); elpi z_report "pp.3" "438" ltac_term:(G)) | idtac "SSR	pp.3	438	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ false _ _ _ X _ _) _)); elpi z_report "pp.3" "439" ltac_term:(G)) | idtac "SSR	pp.3	439	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _)); elpi z_report "pp.3" "440" ltac_term:(G)) | idtac "SSR	pp.3	440	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false false _ _ _ _ X _); elpi z_report "pp.3" "441" ltac_term:(G)) | idtac "SSR	pp.3	441	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ _ X _) (String _ "")); elpi z_report "pp.3" "442" ltac_term:(G)) | idtac "SSR	pp.3	442	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ false _ _ _ _ X _) _)); elpi z_report "pp.3" "443" ltac_term:(G)) | idtac "SSR	pp.3	443	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {28}(false); elpi z_report "pp.3" "444" ltac_term:(G)) | idtac "SSR	pp.3	444	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {28}(false); elpi z_report "pp.3" "445" ltac_term:(G)) | idtac "SSR	pp.3	445	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii false false _ _ _ _ X _); elpi z_report "pp.3" "446" ltac_term:(G)) | idtac "SSR	pp.3	446	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ _ _ _ _ _ X _) (String _ "")); elpi z_report "pp.3" "447" ltac_term:(G)) | idtac "SSR	pp.3	447	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ false _ _ _ _ X _) _)); elpi z_report "pp.3" "448" ltac_term:(G)) | idtac "SSR	pp.3	448	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _)); elpi z_report "pp.3" "449" ltac_term:(G)) | idtac "SSR	pp.3	449	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ _ _ _ _ _ false X); elpi z_report "pp.3" "450" ltac_term:(G)) | idtac "SSR	pp.3	450	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ _ false X) _); elpi z_report "pp.3" "451" ltac_term:(G)) | idtac "SSR	pp.3	451	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ false _ _ _ _ _ X) _)); elpi z_report "pp.3" "452" ltac_term:(G)) | idtac "SSR	pp.3	452	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {29}(false); elpi z_report "pp.3" "453" ltac_term:(G)) | idtac "SSR	pp.3	453	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {29}(false); elpi z_report "pp.3" "454" ltac_term:(G)) | idtac "SSR	pp.3	454	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ _ _ _ _ _ false X); elpi z_report "pp.3" "455" ltac_term:(G)) | idtac "SSR	pp.3	455	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ _ _ _ _ _ false X) _); elpi z_report "pp.3" "456" ltac_term:(G)) | idtac "SSR	pp.3	456	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ false _ _ _ _ _ X) _)); elpi z_report "pp.3" "457" ltac_term:(G)) | idtac "SSR	pp.3	457	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ "" in X in _ = X); elpi z_report "pp.3" "458" ltac_term:(G)) | idtac "SSR	pp.3	458	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ X)); elpi z_report "pp.3" "459" ltac_term:(G)) | idtac "SSR	pp.3	459	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ "" in X in _ = String _ X); elpi z_report "pp.3" "460" ltac_term:(G)) | idtac "SSR	pp.3	460	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in _ = String _ (String _ X)); elpi z_report "pp.3" "461" ltac_term:(G)) | idtac "SSR	pp.3	461	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ ""); elpi z_report "pp.3" "462" ltac_term:(G)) | idtac "SSR	pp.3	462	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ "" as X in String _ X); elpi z_report "pp.3" "463" ltac_term:(G)) | idtac "SSR	pp.3	463	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ _ _ _ _ _ false _) X); elpi z_report "pp.3" "464" ltac_term:(G)) | idtac "SSR	pp.3	464	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ _ as X in String _ (String _ X)); elpi z_report "pp.3" "465" ltac_term:(G)) | idtac "SSR	pp.3	465	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii true _ _ _ _ _ _ _) (String _ X)); elpi z_report "pp.3" "466" ltac_term:(G)) | idtac "SSR	pp.3	466	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String _ "" in X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "467" ltac_term:(G)) | idtac "SSR	pp.3	467	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}("b"%string); elpi z_report "pp.3" "468" ltac_term:(G)) | idtac "SSR	pp.3	468	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String _ ""); elpi z_report "pp.3" "469" ltac_term:(G)) | idtac "SSR	pp.3	469	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String _ "" as X in String _ X); elpi z_report "pp.3" "470" ltac_term:(G)) | idtac "SSR	pp.3	470	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ _ _ _ _ _ false _) X); elpi z_report "pp.3" "471" ltac_term:(G)) | idtac "SSR	pp.3	471	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String _ _ as X in String _ (String _ X)); elpi z_report "pp.3" "472" ltac_term:(G)) | idtac "SSR	pp.3	472	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii true _ _ _ _ _ _ _) (String _ X)); elpi z_report "pp.3" "473" ltac_term:(G)) | idtac "SSR	pp.3	473	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(String _ "" in X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "474" ltac_term:(G)) | idtac "SSR	pp.3	474	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (String); elpi z_report "pp.3" "475" ltac_term:(G)) | idtac "SSR	pp.3	475	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(String); elpi z_report "pp.3" "476" ltac_term:(G)) | idtac "SSR	pp.3	476	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(String); elpi z_report "pp.3" "477" ltac_term:(G)) | idtac "SSR	pp.3	477	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ in X in _ = X); elpi z_report "pp.3" "478" ltac_term:(G)) | idtac "SSR	pp.3	478	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ in X in _ = String _ X); elpi z_report "pp.3" "479" ltac_term:(G)) | idtac "SSR	pp.3	479	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String X _))); elpi z_report "pp.3" "480" ltac_term:(G)) | idtac "SSR	pp.3	480	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in _ = String _ (String _ (String X _))); elpi z_report "pp.3" "481" ltac_term:(G)) | idtac "SSR	pp.3	481	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _); elpi z_report "pp.3" "482" ltac_term:(G)) | idtac "SSR	pp.3	482	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String X ""); elpi z_report "pp.3" "483" ltac_term:(G)) | idtac "SSR	pp.3	483	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "484" ltac_term:(G)) | idtac "SSR	pp.3	484	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String X "")); elpi z_report "pp.3" "485" ltac_term:(G)) | idtac "SSR	pp.3	485	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String X _))); elpi z_report "pp.3" "486" ltac_term:(G)) | idtac "SSR	pp.3	486	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii _ _ _ _ _ _ false _) X); elpi z_report "pp.3" "487" ltac_term:(G)) | idtac "SSR	pp.3	487	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ as X in String _ (String X _)); elpi z_report "pp.3" "488" ltac_term:(G)) | idtac "SSR	pp.3	488	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ as X in String _ (String _ (String X _))); elpi z_report "pp.3" "489" ltac_term:(G)) | idtac "SSR	pp.3	489	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ true _ _ _ _ _ _ in X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "490" ltac_term:(G)) | idtac "SSR	pp.3	490	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii true _ _ _ _ _ _ _) (String _ X)); elpi z_report "pp.3" "491" ltac_term:(G)) | idtac "SSR	pp.3	491	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ true _ _ _ _ _ _); elpi z_report "pp.3" "492" ltac_term:(G)) | idtac "SSR	pp.3	492	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String X ""); elpi z_report "pp.3" "493" ltac_term:(G)) | idtac "SSR	pp.3	493	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ true _ _ _ _ _ _ as X in String X _); elpi z_report "pp.3" "494" ltac_term:(G)) | idtac "SSR	pp.3	494	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String X "")); elpi z_report "pp.3" "495" ltac_term:(G)) | idtac "SSR	pp.3	495	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String X _))); elpi z_report "pp.3" "496" ltac_term:(G)) | idtac "SSR	pp.3	496	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii _ _ _ _ _ _ false _) X); elpi z_report "pp.3" "497" ltac_term:(G)) | idtac "SSR	pp.3	497	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ true _ _ _ _ _ _ as X in String _ (String X _)); elpi z_report "pp.3" "498" ltac_term:(G)) | idtac "SSR	pp.3	498	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ _ _ _ _ _ _ _ as X in String _ (String _ (String X _))); elpi z_report "pp.3" "499" ltac_term:(G)) | idtac "SSR	pp.3	499	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ true _ _ _ _ _ _ in X in String (Ascii.Ascii true _ _ _ _ _ _ _) X); elpi z_report "pp.3" "500" ltac_term:(G)) | idtac "SSR	pp.3	500	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii _ _ _ _ _ _ _ _ in X in String (Ascii.Ascii true _ _ _ _ _ _ _) (String _ X)); elpi z_report "pp.3" "501" ltac_term:(G)) | idtac "SSR	pp.3	501	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Ascii.Ascii false true false false false true true false); elpi z_report "pp.3" "502" ltac_term:(G)) | idtac "SSR	pp.3	502	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Ascii.Ascii); elpi z_report "pp.3" "503" ltac_term:(G)) | idtac "SSR	pp.3	503	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(Ascii.Ascii); elpi z_report "pp.3" "504" ltac_term:(G)) | idtac "SSR	pp.3	504	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(Ascii.Ascii); elpi z_report "pp.3" "505" ltac_term:(G)) | idtac "SSR	pp.3	505	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _))); elpi z_report "pp.3" "506" ltac_term:(G)) | idtac "SSR	pp.3	506	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii X true _ _ _ _ _ _); elpi z_report "pp.3" "507" ltac_term:(G)) | idtac "SSR	pp.3	507	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii X true _ _ _ _ _ _) _); elpi z_report "pp.3" "508" ltac_term:(G)) | idtac "SSR	pp.3	508	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii X true _ _ _ _ _ _) _)); elpi z_report "pp.3" "509" ltac_term:(G)) | idtac "SSR	pp.3	509	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _))); elpi z_report "pp.3" "510" ltac_term:(G)) | idtac "SSR	pp.3	510	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {30}(false); elpi z_report "pp.3" "511" ltac_term:(G)) | idtac "SSR	pp.3	511	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {30}(false); elpi z_report "pp.3" "512" ltac_term:(G)) | idtac "SSR	pp.3	512	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii X true _ _ _ _ _ _); elpi z_report "pp.3" "513" ltac_term:(G)) | idtac "SSR	pp.3	513	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii X true _ _ _ _ _ _) _); elpi z_report "pp.3" "514" ltac_term:(G)) | idtac "SSR	pp.3	514	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii X true _ _ _ _ _ _) _)); elpi z_report "pp.3" "515" ltac_term:(G)) | idtac "SSR	pp.3	515	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii X _ _ _ _ _ _ _) _))); elpi z_report "pp.3" "516" ltac_term:(G)) | idtac "SSR	pp.3	516	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _))); elpi z_report "pp.3" "517" ltac_term:(G)) | idtac "SSR	pp.3	517	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii false X _ _ _ _ true _); elpi z_report "pp.3" "518" ltac_term:(G)) | idtac "SSR	pp.3	518	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ X _ _ _ _ _ _) ""); elpi z_report "pp.3" "519" ltac_term:(G)) | idtac "SSR	pp.3	519	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ X _ _ _ _ true _) _)); elpi z_report "pp.3" "520" ltac_term:(G)) | idtac "SSR	pp.3	520	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _))); elpi z_report "pp.3" "521" ltac_term:(G)) | idtac "SSR	pp.3	521	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {12}(true); elpi z_report "pp.3" "522" ltac_term:(G)) | idtac "SSR	pp.3	522	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {12}(true); elpi z_report "pp.3" "523" ltac_term:(G)) | idtac "SSR	pp.3	523	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii false X _ _ _ _ true _); elpi z_report "pp.3" "524" ltac_term:(G)) | idtac "SSR	pp.3	524	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ X _ _ _ _ _ _) ""); elpi z_report "pp.3" "525" ltac_term:(G)) | idtac "SSR	pp.3	525	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ X _ _ _ _ true _) _)); elpi z_report "pp.3" "526" ltac_term:(G)) | idtac "SSR	pp.3	526	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii _ X _ _ _ _ _ _) _))); elpi z_report "pp.3" "527" ltac_term:(G)) | idtac "SSR	pp.3	527	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _))); elpi z_report "pp.3" "528" ltac_term:(G)) | idtac "SSR	pp.3	528	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ true X _ _ _ _ _); elpi z_report "pp.3" "529" ltac_term:(G)) | idtac "SSR	pp.3	529	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ true X _ _ _ _ _) _); elpi z_report "pp.3" "530" ltac_term:(G)) | idtac "SSR	pp.3	530	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ true X _ _ _ _ _) _)); elpi z_report "pp.3" "531" ltac_term:(G)) | idtac "SSR	pp.3	531	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _))); elpi z_report "pp.3" "532" ltac_term:(G)) | idtac "SSR	pp.3	532	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {31}(false); elpi z_report "pp.3" "533" ltac_term:(G)) | idtac "SSR	pp.3	533	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {31}(false); elpi z_report "pp.3" "534" ltac_term:(G)) | idtac "SSR	pp.3	534	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ true X _ _ _ _ _); elpi z_report "pp.3" "535" ltac_term:(G)) | idtac "SSR	pp.3	535	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ true X _ _ _ _ _) _); elpi z_report "pp.3" "536" ltac_term:(G)) | idtac "SSR	pp.3	536	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ true X _ _ _ _ _) _)); elpi z_report "pp.3" "537" ltac_term:(G)) | idtac "SSR	pp.3	537	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii _ _ X _ _ _ _ _) _))); elpi z_report "pp.3" "538" ltac_term:(G)) | idtac "SSR	pp.3	538	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _))); elpi z_report "pp.3" "539" ltac_term:(G)) | idtac "SSR	pp.3	539	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ true _ X _ _ _ _); elpi z_report "pp.3" "540" ltac_term:(G)) | idtac "SSR	pp.3	540	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ true _ X _ _ _ _) _); elpi z_report "pp.3" "541" ltac_term:(G)) | idtac "SSR	pp.3	541	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ true _ X _ _ _ _) _)); elpi z_report "pp.3" "542" ltac_term:(G)) | idtac "SSR	pp.3	542	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _))); elpi z_report "pp.3" "543" ltac_term:(G)) | idtac "SSR	pp.3	543	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {32}(false); elpi z_report "pp.3" "544" ltac_term:(G)) | idtac "SSR	pp.3	544	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {32}(false); elpi z_report "pp.3" "545" ltac_term:(G)) | idtac "SSR	pp.3	545	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ true _ X _ _ _ _); elpi z_report "pp.3" "546" ltac_term:(G)) | idtac "SSR	pp.3	546	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ true _ X _ _ _ _) _); elpi z_report "pp.3" "547" ltac_term:(G)) | idtac "SSR	pp.3	547	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ true _ X _ _ _ _) _)); elpi z_report "pp.3" "548" ltac_term:(G)) | idtac "SSR	pp.3	548	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii _ _ _ X _ _ _ _) _))); elpi z_report "pp.3" "549" ltac_term:(G)) | idtac "SSR	pp.3	549	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _))); elpi z_report "pp.3" "550" ltac_term:(G)) | idtac "SSR	pp.3	550	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ true _ _ X _ _ _); elpi z_report "pp.3" "551" ltac_term:(G)) | idtac "SSR	pp.3	551	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ true _ _ X _ _ _) _); elpi z_report "pp.3" "552" ltac_term:(G)) | idtac "SSR	pp.3	552	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ true _ _ X _ _ _) _)); elpi z_report "pp.3" "553" ltac_term:(G)) | idtac "SSR	pp.3	553	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _))); elpi z_report "pp.3" "554" ltac_term:(G)) | idtac "SSR	pp.3	554	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {33}(false); elpi z_report "pp.3" "555" ltac_term:(G)) | idtac "SSR	pp.3	555	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {33}(false); elpi z_report "pp.3" "556" ltac_term:(G)) | idtac "SSR	pp.3	556	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ true _ _ X _ _ _); elpi z_report "pp.3" "557" ltac_term:(G)) | idtac "SSR	pp.3	557	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ true _ _ X _ _ _) _); elpi z_report "pp.3" "558" ltac_term:(G)) | idtac "SSR	pp.3	558	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ true _ _ X _ _ _) _)); elpi z_report "pp.3" "559" ltac_term:(G)) | idtac "SSR	pp.3	559	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ X _ _ _) _))); elpi z_report "pp.3" "560" ltac_term:(G)) | idtac "SSR	pp.3	560	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _))); elpi z_report "pp.3" "561" ltac_term:(G)) | idtac "SSR	pp.3	561	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ true _ _ _ X _ _); elpi z_report "pp.3" "562" ltac_term:(G)) | idtac "SSR	pp.3	562	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ true _ _ _ X _ _) _); elpi z_report "pp.3" "563" ltac_term:(G)) | idtac "SSR	pp.3	563	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ true _ _ _ X _ _) _)); elpi z_report "pp.3" "564" ltac_term:(G)) | idtac "SSR	pp.3	564	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _))); elpi z_report "pp.3" "565" ltac_term:(G)) | idtac "SSR	pp.3	565	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {13}(true); elpi z_report "pp.3" "566" ltac_term:(G)) | idtac "SSR	pp.3	566	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {13}(true); elpi z_report "pp.3" "567" ltac_term:(G)) | idtac "SSR	pp.3	567	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ true _ _ _ X _ _); elpi z_report "pp.3" "568" ltac_term:(G)) | idtac "SSR	pp.3	568	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ true _ _ _ X _ _) _); elpi z_report "pp.3" "569" ltac_term:(G)) | idtac "SSR	pp.3	569	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ true _ _ _ X _ _) _)); elpi z_report "pp.3" "570" ltac_term:(G)) | idtac "SSR	pp.3	570	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ X _ _) _))); elpi z_report "pp.3" "571" ltac_term:(G)) | idtac "SSR	pp.3	571	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _))); elpi z_report "pp.3" "572" ltac_term:(G)) | idtac "SSR	pp.3	572	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (true); elpi z_report "pp.3" "573" ltac_term:(G)) | idtac "SSR	pp.3	573	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ true _ _ _ _ X _); elpi z_report "pp.3" "574" ltac_term:(G)) | idtac "SSR	pp.3	574	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ true _ _ _ _ X _) _); elpi z_report "pp.3" "575" ltac_term:(G)) | idtac "SSR	pp.3	575	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ true _ _ _ _ X _) _)); elpi z_report "pp.3" "576" ltac_term:(G)) | idtac "SSR	pp.3	576	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _))); elpi z_report "pp.3" "577" ltac_term:(G)) | idtac "SSR	pp.3	577	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {14}(true); elpi z_report "pp.3" "578" ltac_term:(G)) | idtac "SSR	pp.3	578	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {14}(true); elpi z_report "pp.3" "579" ltac_term:(G)) | idtac "SSR	pp.3	579	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ true _ _ _ _ X _); elpi z_report "pp.3" "580" ltac_term:(G)) | idtac "SSR	pp.3	580	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ true _ _ _ _ X _) _); elpi z_report "pp.3" "581" ltac_term:(G)) | idtac "SSR	pp.3	581	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ true _ _ _ _ X _) _)); elpi z_report "pp.3" "582" ltac_term:(G)) | idtac "SSR	pp.3	582	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ X _) _))); elpi z_report "pp.3" "583" ltac_term:(G)) | idtac "SSR	pp.3	583	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _))); elpi z_report "pp.3" "584" ltac_term:(G)) | idtac "SSR	pp.3	584	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (false); elpi z_report "pp.3" "585" ltac_term:(G)) | idtac "SSR	pp.3	585	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Ascii.Ascii _ true _ _ _ _ _ X); elpi z_report "pp.3" "586" ltac_term:(G)) | idtac "SSR	pp.3	586	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ true _ _ _ _ _ X) _); elpi z_report "pp.3" "587" ltac_term:(G)) | idtac "SSR	pp.3	587	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String (Ascii.Ascii _ true _ _ _ _ _ X) _)); elpi z_report "pp.3" "588" ltac_term:(G)) | idtac "SSR	pp.3	588	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _))); elpi z_report "pp.3" "589" ltac_term:(G)) | idtac "SSR	pp.3	589	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {34}(false); elpi z_report "pp.3" "590" ltac_term:(G)) | idtac "SSR	pp.3	590	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {34}(false); elpi z_report "pp.3" "591" ltac_term:(G)) | idtac "SSR	pp.3	591	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in Ascii.Ascii _ true _ _ _ _ _ X); elpi z_report "pp.3" "592" ltac_term:(G)) | idtac "SSR	pp.3	592	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ true _ _ _ _ _ X) _); elpi z_report "pp.3" "593" ltac_term:(G)) | idtac "SSR	pp.3	593	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String (Ascii.Ascii _ true _ _ _ _ _ X) _)); elpi z_report "pp.3" "594" ltac_term:(G)) | idtac "SSR	pp.3	594	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String (Ascii.Ascii _ _ _ _ _ _ _ X) _))); elpi z_report "pp.3" "595" ltac_term:(G)) | idtac "SSR	pp.3	595	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = String _ (String _ (String _ X))); elpi z_report "pp.3" "596" ltac_term:(G)) | idtac "SSR	pp.3	596	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (""%string); elpi z_report "pp.3" "597" ltac_term:(G)) | idtac "SSR	pp.3	597	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii _ true _ _ _ _ _ _) X); elpi z_report "pp.3" "598" ltac_term:(G)) | idtac "SSR	pp.3	598	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String _ (String _ (String _ X))); elpi z_report "pp.3" "599" ltac_term:(G)) | idtac "SSR	pp.3	599	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in String (Ascii.Ascii false _ _ _ _ _ _ _) (String _ X)); elpi z_report "pp.3" "600" ltac_term:(G)) | idtac "SSR	pp.3	600	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(""%string); elpi z_report "pp.3" "601" ltac_term:(G)) | idtac "SSR	pp.3	601	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(""%string); elpi z_report "pp.3" "602" ltac_term:(G)) | idtac "SSR	pp.3	602	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii _ true _ _ _ _ _ _) X); elpi z_report "pp.3" "603" ltac_term:(G)) | idtac "SSR	pp.3	603	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String _ (String _ (String _ X))); elpi z_report "pp.3" "604" ltac_term:(G)) | idtac "SSR	pp.3	604	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in String (Ascii.Ascii false _ _ _ _ _ _ _) (String _ X)); elpi z_report "pp.3" "605" ltac_term:(G)) | idtac "SSR	pp.3	605	error" ].
Abort.

Goal forall (p : nat * nat), (let '(a, b) := p in a + b) = 0 -> True.
intros p H.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (True); elpi z_report "pp.4" "1" ltac_term:(G)) | idtac "SSR	pp.4	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(True); elpi z_report "pp.4" "2" ltac_term:(G)) | idtac "SSR	pp.4	2	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ = _) in H; elpi z_report "pp.4" "3" ltac_term:(G) "H") | idtac "SSR	pp.4	3	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}((let (a, b) := p in a + b) = 0) in H; elpi z_report "pp.4" "4" ltac_term:(G) "H") | idtac "SSR	pp.4	4	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (@eq) in H; elpi z_report "pp.4" "5" ltac_term:(G) "H") | idtac "SSR	pp.4	5	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H; elpi z_report "pp.4" "6" ltac_term:(G) "H") | idtac "SSR	pp.4	6	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H; elpi z_report "pp.4" "7" ltac_term:(G) "H") | idtac "SSR	pp.4	7	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H; elpi z_report "pp.4" "8" ltac_term:(G) "H") | idtac "SSR	pp.4	8	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in X = _) in H; elpi z_report "pp.4" "9" ltac_term:(G) "H") | idtac "SSR	pp.4	9	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (let (a, b) := p in a + b) in H; elpi z_report "pp.4" "10" ltac_term:(G) "H") | idtac "SSR	pp.4	10	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(let (a, b) := p in a + b) in H; elpi z_report "pp.4" "11" ltac_term:(G) "H") | idtac "SSR	pp.4	11	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (p) in H; elpi z_report "pp.4" "12" ltac_term:(G) "H") | idtac "SSR	pp.4	12	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(p) in H; elpi z_report "pp.4" "13" ltac_term:(G) "H") | idtac "SSR	pp.4	13	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (nat) in H; elpi z_report "pp.4" "14" ltac_term:(G) "H") | idtac "SSR	pp.4	14	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H; elpi z_report "pp.4" "15" ltac_term:(G) "H") | idtac "SSR	pp.4	15	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H; elpi z_report "pp.4" "16" ltac_term:(G) "H") | idtac "SSR	pp.4	16	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (Nat.add) in H; elpi z_report "pp.4" "17" ltac_term:(G) "H") | idtac "SSR	pp.4	17	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H; elpi z_report "pp.4" "18" ltac_term:(G) "H") | idtac "SSR	pp.4	18	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (0) in H; elpi z_report "pp.4" "19" ltac_term:(G) "H") | idtac "SSR	pp.4	19	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = X) in H; elpi z_report "pp.4" "20" ltac_term:(G) "H") | idtac "SSR	pp.4	20	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(0) in H; elpi z_report "pp.4" "21" ltac_term:(G) "H") | idtac "SSR	pp.4	21	error" ].
Abort.

Goal forall (n : nat) (b : bool), match n with 0 => true | S k => Nat.eqb k n end = (if b then false else true).
intros n b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.5" "1" ltac_term:(G)) | idtac "SSR	pp.5	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(match n with | 0 => true | S k => Nat.eqb k n end = (if b then false else true)); elpi z_report "pp.5" "2" ltac_term:(G)) | idtac "SSR	pp.5	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.5" "3" ltac_term:(G)) | idtac "SSR	pp.5	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.5" "4" ltac_term:(G)) | idtac "SSR	pp.5	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.5" "5" ltac_term:(G)) | idtac "SSR	pp.5	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.5" "6" ltac_term:(G)) | idtac "SSR	pp.5	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.5" "7" ltac_term:(G)) | idtac "SSR	pp.5	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (match n with | 0 => true | S k => Nat.eqb k n end); elpi z_report "pp.5" "8" ltac_term:(G)) | idtac "SSR	pp.5	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(match n with | 0 => true | S k => Nat.eqb k n end); elpi z_report "pp.5" "9" ltac_term:(G)) | idtac "SSR	pp.5	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.5" "10" ltac_term:(G)) | idtac "SSR	pp.5	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.5" "11" ltac_term:(G)) | idtac "SSR	pp.5	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.5" "12" ltac_term:(G)) | idtac "SSR	pp.5	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.5" "13" ltac_term:(G)) | idtac "SSR	pp.5	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.5" "14" ltac_term:(G)) | idtac "SSR	pp.5	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.5" "15" ltac_term:(G)) | idtac "SSR	pp.5	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.eqb); elpi z_report "pp.5" "16" ltac_term:(G)) | idtac "SSR	pp.5	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.eqb); elpi z_report "pp.5" "17" ltac_term:(G)) | idtac "SSR	pp.5	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.5" "18" ltac_term:(G)) | idtac "SSR	pp.5	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.5" "19" ltac_term:(G)) | idtac "SSR	pp.5	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.5" "20" ltac_term:(G)) | idtac "SSR	pp.5	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.5" "21" ltac_term:(G)) | idtac "SSR	pp.5	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (if b then false else true); elpi z_report "pp.5" "22" ltac_term:(G)) | idtac "SSR	pp.5	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(if b then false else true); elpi z_report "pp.5" "23" ltac_term:(G)) | idtac "SSR	pp.5	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.5" "24" ltac_term:(G)) | idtac "SSR	pp.5	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.5" "25" ltac_term:(G)) | idtac "SSR	pp.5	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (bool); elpi z_report "pp.5" "26" ltac_term:(G)) | idtac "SSR	pp.5	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(bool); elpi z_report "pp.5" "27" ltac_term:(G)) | idtac "SSR	pp.5	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(bool); elpi z_report "pp.5" "28" ltac_term:(G)) | idtac "SSR	pp.5	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (false); elpi z_report "pp.5" "29" ltac_term:(G)) | idtac "SSR	pp.5	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(false); elpi z_report "pp.5" "30" ltac_term:(G)) | idtac "SSR	pp.5	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (true); elpi z_report "pp.5" "31" ltac_term:(G)) | idtac "SSR	pp.5	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.5" "32" ltac_term:(G)) | idtac "SSR	pp.5	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.5" "33" ltac_term:(G)) | idtac "SSR	pp.5	33	error" ].
Abort.

Goal forall (b : bool), match b as x return (if x then nat else bool) with true => 0 | false => true end = match b as x return (if x then nat else bool) with true => 0 | false => true end.
intros b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.6" "1" ltac_term:(G)) | idtac "SSR	pp.6	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((if b as x return (if x then nat else bool) then 0 else true) = (if b as x return (if x then nat else bool) then 0 else true)); elpi z_report "pp.6" "2" ltac_term:(G)) | idtac "SSR	pp.6	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.6" "3" ltac_term:(G)) | idtac "SSR	pp.6	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.6" "4" ltac_term:(G)) | idtac "SSR	pp.6	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (if b then nat else bool); elpi z_report "pp.6" "5" ltac_term:(G)) | idtac "SSR	pp.6	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(if b then nat else bool); elpi z_report "pp.6" "6" ltac_term:(G)) | idtac "SSR	pp.6	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.6" "7" ltac_term:(G)) | idtac "SSR	pp.6	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.6" "8" ltac_term:(G)) | idtac "SSR	pp.6	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Set); elpi z_report "pp.6" "9" ltac_term:(G)) | idtac "SSR	pp.6	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Set); elpi z_report "pp.6" "10" ltac_term:(G)) | idtac "SSR	pp.6	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.6" "11" ltac_term:(G)) | idtac "SSR	pp.6	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.6" "12" ltac_term:(G)) | idtac "SSR	pp.6	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.6" "13" ltac_term:(G)) | idtac "SSR	pp.6	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.6" "14" ltac_term:(G)) | idtac "SSR	pp.6	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.6" "15" ltac_term:(G)) | idtac "SSR	pp.6	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(if b as x return (if x then nat else bool) then 0 else true); elpi z_report "pp.6" "16" ltac_term:(G)) | idtac "SSR	pp.6	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(if b as x return (if x then nat else bool) then 0 else true); elpi z_report "pp.6" "17" ltac_term:(G)) | idtac "SSR	pp.6	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.6" "18" ltac_term:(G)) | idtac "SSR	pp.6	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.6" "19" ltac_term:(G)) | idtac "SSR	pp.6	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Set); elpi z_report "pp.6" "20" ltac_term:(G)) | idtac "SSR	pp.6	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Set); elpi z_report "pp.6" "21" ltac_term:(G)) | idtac "SSR	pp.6	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.6" "22" ltac_term:(G)) | idtac "SSR	pp.6	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.6" "23" ltac_term:(G)) | idtac "SSR	pp.6	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.6" "24" ltac_term:(G)) | idtac "SSR	pp.6	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.6" "25" ltac_term:(G)) | idtac "SSR	pp.6	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.6" "26" ltac_term:(G)) | idtac "SSR	pp.6	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.6" "27" ltac_term:(G)) | idtac "SSR	pp.6	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.6" "28" ltac_term:(G)) | idtac "SSR	pp.6	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.6" "29" ltac_term:(G)) | idtac "SSR	pp.6	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.6" "30" ltac_term:(G)) | idtac "SSR	pp.6	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (if b as x return (if x then nat else bool) then 0 else true); elpi z_report "pp.6" "31" ltac_term:(G)) | idtac "SSR	pp.6	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(if b as x return (if x then nat else bool) then 0 else true); elpi z_report "pp.6" "32" ltac_term:(G)) | idtac "SSR	pp.6	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(if b as x return (if x then nat else bool) then 0 else true); elpi z_report "pp.6" "33" ltac_term:(G)) | idtac "SSR	pp.6	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.6" "34" ltac_term:(G)) | idtac "SSR	pp.6	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "pp.6" "35" ltac_term:(G)) | idtac "SSR	pp.6	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "pp.6" "36" ltac_term:(G)) | idtac "SSR	pp.6	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Set); elpi z_report "pp.6" "37" ltac_term:(G)) | idtac "SSR	pp.6	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Set); elpi z_report "pp.6" "38" ltac_term:(G)) | idtac "SSR	pp.6	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Set); elpi z_report "pp.6" "39" ltac_term:(G)) | idtac "SSR	pp.6	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.6" "40" ltac_term:(G)) | idtac "SSR	pp.6	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.6" "41" ltac_term:(G)) | idtac "SSR	pp.6	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.6" "42" ltac_term:(G)) | idtac "SSR	pp.6	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (bool); elpi z_report "pp.6" "43" ltac_term:(G)) | idtac "SSR	pp.6	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(bool); elpi z_report "pp.6" "44" ltac_term:(G)) | idtac "SSR	pp.6	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(bool); elpi z_report "pp.6" "45" ltac_term:(G)) | idtac "SSR	pp.6	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.6" "46" ltac_term:(G)) | idtac "SSR	pp.6	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.6" "47" ltac_term:(G)) | idtac "SSR	pp.6	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.6" "48" ltac_term:(G)) | idtac "SSR	pp.6	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (true); elpi z_report "pp.6" "49" ltac_term:(G)) | idtac "SSR	pp.6	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.6" "50" ltac_term:(G)) | idtac "SSR	pp.6	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.6" "51" ltac_term:(G)) | idtac "SSR	pp.6	51	error" ].
Abort.

Goal forall x : nat, (forall x : nat, x = x) -> forall y, (fun x => x + y) x = x.
intros x H.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (forall y : nat, [elpi_ctx_entry_3_ : nat in elpi_ctx_entry_3_ + y] x = x); elpi z_report "pp.7" "1" ltac_term:(G)) | idtac "SSR	pp.7	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(forall y : nat, [elpi_ctx_entry_3_ : nat in elpi_ctx_entry_3_ + y] x = x); elpi z_report "pp.7" "2" ltac_term:(G)) | idtac "SSR	pp.7	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.7" "3" ltac_term:(G)) | idtac "SSR	pp.7	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.7" "4" ltac_term:(G)) | idtac "SSR	pp.7	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.7" "5" ltac_term:(G)) | idtac "SSR	pp.7	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.7" "6" ltac_term:(G)) | idtac "SSR	pp.7	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.7" "7" ltac_term:(G)) | idtac "SSR	pp.7	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.7" "8" ltac_term:(G)) | idtac "SSR	pp.7	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.7" "9" ltac_term:(G)) | idtac "SSR	pp.7	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.7" "10" ltac_term:(G)) | idtac "SSR	pp.7	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.7" "11" ltac_term:(G)) | idtac "SSR	pp.7	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.7" "12" ltac_term:(G)) | idtac "SSR	pp.7	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.7" "13" ltac_term:(G)) | idtac "SSR	pp.7	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(x); elpi z_report "pp.7" "14" ltac_term:(G)) | idtac "SSR	pp.7	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(x); elpi z_report "pp.7" "15" ltac_term:(G)) | idtac "SSR	pp.7	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (x); elpi z_report "pp.7" "16" ltac_term:(G)) | idtac "SSR	pp.7	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(x); elpi z_report "pp.7" "17" ltac_term:(G)) | idtac "SSR	pp.7	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(x); elpi z_report "pp.7" "18" ltac_term:(G)) | idtac "SSR	pp.7	18	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (forall elpi_ctx_entry_2_ : nat, elpi_ctx_entry_2_ = elpi_ctx_entry_2_) in H; elpi z_report "pp.7" "19" ltac_term:(G) "H") | idtac "SSR	pp.7	19	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(forall elpi_ctx_entry_2_ : nat, elpi_ctx_entry_2_ = elpi_ctx_entry_2_) in H; elpi z_report "pp.7" "20" ltac_term:(G) "H") | idtac "SSR	pp.7	20	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H; elpi z_report "pp.7" "21" ltac_term:(G) "H") | idtac "SSR	pp.7	21	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H; elpi z_report "pp.7" "22" ltac_term:(G) "H") | idtac "SSR	pp.7	22	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (@eq) in H; elpi z_report "pp.7" "23" ltac_term:(G) "H") | idtac "SSR	pp.7	23	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H; elpi z_report "pp.7" "24" ltac_term:(G) "H") | idtac "SSR	pp.7	24	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (nat) in H; elpi z_report "pp.7" "25" ltac_term:(G) "H") | idtac "SSR	pp.7	25	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H; elpi z_report "pp.7" "26" ltac_term:(G) "H") | idtac "SSR	pp.7	26	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H; elpi z_report "pp.7" "27" ltac_term:(G) "H") | idtac "SSR	pp.7	27	error" ].
Abort.

Goal forall (a b : nat) (c d : bool), (fun x y : nat => x + y) a b = a + b /\ exists (u v : nat) (w : bool), u = v /\ w = c.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (forall (a b : nat) (c : bool), bool -> [x y : nat in x + y] a b = a + b /\ (exists (u v : nat) (w : bool), u = v /\ w = c)); elpi z_report "pp.8" "1" ltac_term:(G)) | idtac "SSR	pp.8	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(forall (a b : nat) (c : bool), bool -> [x y : nat in x + y] a b = a + b /\ (exists (u v : nat) (w : bool), u = v /\ w = c)); elpi z_report "pp.8" "2" ltac_term:(G)) | idtac "SSR	pp.8	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.8" "3" ltac_term:(G)) | idtac "SSR	pp.8	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.8" "4" ltac_term:(G)) | idtac "SSR	pp.8	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.8" "5" ltac_term:(G)) | idtac "SSR	pp.8	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.8" "6" ltac_term:(G)) | idtac "SSR	pp.8	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.8" "7" ltac_term:(G)) | idtac "SSR	pp.8	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.8" "8" ltac_term:(G)) | idtac "SSR	pp.8	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.8" "9" ltac_term:(G)) | idtac "SSR	pp.8	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.8" "10" ltac_term:(G)) | idtac "SSR	pp.8	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "pp.8" "11" ltac_term:(G)) | idtac "SSR	pp.8	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "pp.8" "12" ltac_term:(G)) | idtac "SSR	pp.8	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.8" "13" ltac_term:(G)) | idtac "SSR	pp.8	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.8" "14" ltac_term:(G)) | idtac "SSR	pp.8	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.8" "15" ltac_term:(G)) | idtac "SSR	pp.8	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.8" "16" ltac_term:(G)) | idtac "SSR	pp.8	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "pp.8" "17" ltac_term:(G)) | idtac "SSR	pp.8	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "pp.8" "18" ltac_term:(G)) | idtac "SSR	pp.8	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(nat); elpi z_report "pp.8" "19" ltac_term:(G)) | idtac "SSR	pp.8	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(nat); elpi z_report "pp.8" "20" ltac_term:(G)) | idtac "SSR	pp.8	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.8" "21" ltac_term:(G)) | idtac "SSR	pp.8	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.8" "22" ltac_term:(G)) | idtac "SSR	pp.8	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.8" "23" ltac_term:(G)) | idtac "SSR	pp.8	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "pp.8" "24" ltac_term:(G)) | idtac "SSR	pp.8	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "pp.8" "25" ltac_term:(G)) | idtac "SSR	pp.8	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(ex); elpi z_report "pp.8" "26" ltac_term:(G)) | idtac "SSR	pp.8	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(ex); elpi z_report "pp.8" "27" ltac_term:(G)) | idtac "SSR	pp.8	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(nat); elpi z_report "pp.8" "28" ltac_term:(G)) | idtac "SSR	pp.8	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(nat); elpi z_report "pp.8" "29" ltac_term:(G)) | idtac "SSR	pp.8	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(nat); elpi z_report "pp.8" "30" ltac_term:(G)) | idtac "SSR	pp.8	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(nat); elpi z_report "pp.8" "31" ltac_term:(G)) | idtac "SSR	pp.8	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(ex); elpi z_report "pp.8" "32" ltac_term:(G)) | idtac "SSR	pp.8	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(ex); elpi z_report "pp.8" "33" ltac_term:(G)) | idtac "SSR	pp.8	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(nat); elpi z_report "pp.8" "34" ltac_term:(G)) | idtac "SSR	pp.8	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {8}(nat); elpi z_report "pp.8" "35" ltac_term:(G)) | idtac "SSR	pp.8	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(nat); elpi z_report "pp.8" "36" ltac_term:(G)) | idtac "SSR	pp.8	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {9}(nat); elpi z_report "pp.8" "37" ltac_term:(G)) | idtac "SSR	pp.8	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (ex); elpi z_report "pp.8" "38" ltac_term:(G)) | idtac "SSR	pp.8	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(ex); elpi z_report "pp.8" "39" ltac_term:(G)) | idtac "SSR	pp.8	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(ex); elpi z_report "pp.8" "40" ltac_term:(G)) | idtac "SSR	pp.8	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(bool); elpi z_report "pp.8" "41" ltac_term:(G)) | idtac "SSR	pp.8	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(bool); elpi z_report "pp.8" "42" ltac_term:(G)) | idtac "SSR	pp.8	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(bool); elpi z_report "pp.8" "43" ltac_term:(G)) | idtac "SSR	pp.8	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(bool); elpi z_report "pp.8" "44" ltac_term:(G)) | idtac "SSR	pp.8	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "pp.8" "45" ltac_term:(G)) | idtac "SSR	pp.8	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(and); elpi z_report "pp.8" "46" ltac_term:(G)) | idtac "SSR	pp.8	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(and); elpi z_report "pp.8" "47" ltac_term:(G)) | idtac "SSR	pp.8	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.8" "48" ltac_term:(G)) | idtac "SSR	pp.8	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.8" "49" ltac_term:(G)) | idtac "SSR	pp.8	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.8" "50" ltac_term:(G)) | idtac "SSR	pp.8	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(nat); elpi z_report "pp.8" "51" ltac_term:(G)) | idtac "SSR	pp.8	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {10}(nat); elpi z_report "pp.8" "52" ltac_term:(G)) | idtac "SSR	pp.8	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.8" "53" ltac_term:(G)) | idtac "SSR	pp.8	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(@eq); elpi z_report "pp.8" "54" ltac_term:(G)) | idtac "SSR	pp.8	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(@eq); elpi z_report "pp.8" "55" ltac_term:(G)) | idtac "SSR	pp.8	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (bool); elpi z_report "pp.8" "56" ltac_term:(G)) | idtac "SSR	pp.8	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(bool); elpi z_report "pp.8" "57" ltac_term:(G)) | idtac "SSR	pp.8	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(bool); elpi z_report "pp.8" "58" ltac_term:(G)) | idtac "SSR	pp.8	58	error" ].
Abort.

Goal forall n : nat, (n : nat) = n.
intros n.
change ((n : nat) = n).
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.9" "1" ltac_term:(G)) | idtac "SSR	pp.9	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((n : nat) = n); elpi z_report "pp.9" "2" ltac_term:(G)) | idtac "SSR	pp.9	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.9" "3" ltac_term:(G)) | idtac "SSR	pp.9	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.9" "4" ltac_term:(G)) | idtac "SSR	pp.9	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.9" "5" ltac_term:(G)) | idtac "SSR	pp.9	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.9" "6" ltac_term:(G)) | idtac "SSR	pp.9	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.9" "7" ltac_term:(G)) | idtac "SSR	pp.9	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.9" "8" ltac_term:(G)) | idtac "SSR	pp.9	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.9" "9" ltac_term:(G)) | idtac "SSR	pp.9	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.9" "10" ltac_term:(G)) | idtac "SSR	pp.9	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.9" "11" ltac_term:(G)) | idtac "SSR	pp.9	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.9" "12" ltac_term:(G)) | idtac "SSR	pp.9	12	error" ].
Abort.

Module C.
From Stdlib Require Import ZArith.
Coercion Z.of_nat : nat >-> Z.
Record box := Box { unbox :> nat }.
Goal forall (n : nat) (b : box), (n + 1 = b)%Z /\ b + 0 = n.
intros n b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "pp.10" "1" ltac_term:(G)) | idtac "SSR	pp.10	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((n + 1)%Z = b /\ b + 0 = n); elpi z_report "pp.10" "2" ltac_term:(G)) | idtac "SSR	pp.10	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "pp.10" "3" ltac_term:(G)) | idtac "SSR	pp.10	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "pp.10" "4" ltac_term:(G)) | idtac "SSR	pp.10	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.10" "5" ltac_term:(G)) | idtac "SSR	pp.10	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "pp.10" "6" ltac_term:(G)) | idtac "SSR	pp.10	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "pp.10" "7" ltac_term:(G)) | idtac "SSR	pp.10	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((n + 1)%Z = b); elpi z_report "pp.10" "8" ltac_term:(G)) | idtac "SSR	pp.10	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.10" "9" ltac_term:(G)) | idtac "SSR	pp.10	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.10" "10" ltac_term:(G)) | idtac "SSR	pp.10	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z); elpi z_report "pp.10" "11" ltac_term:(G)) | idtac "SSR	pp.10	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Z); elpi z_report "pp.10" "12" ltac_term:(G)) | idtac "SSR	pp.10	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.10" "13" ltac_term:(G)) | idtac "SSR	pp.10	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_ + _)%Z); elpi z_report "pp.10" "14" ltac_term:(G)) | idtac "SSR	pp.10	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "pp.10" "15" ltac_term:(G)) | idtac "SSR	pp.10	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_ + _)%Z as X in X = _); elpi z_report "pp.10" "16" ltac_term:(G)) | idtac "SSR	pp.10	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_ + _)%Z in X in X /\ _); elpi z_report "pp.10" "17" ltac_term:(G)) | idtac "SSR	pp.10	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_ + _)%Z as X in X = _ /\ _); elpi z_report "pp.10" "18" ltac_term:(G)) | idtac "SSR	pp.10	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((n + 1)%Z); elpi z_report "pp.10" "19" ltac_term:(G)) | idtac "SSR	pp.10	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.add); elpi z_report "pp.10" "20" ltac_term:(G)) | idtac "SSR	pp.10	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Z.add); elpi z_report "pp.10" "21" ltac_term:(G)) | idtac "SSR	pp.10	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _); elpi z_report "pp.10" "22" ltac_term:(G)) | idtac "SSR	pp.10	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (X + _)%Z); elpi z_report "pp.10" "23" ltac_term:(G)) | idtac "SSR	pp.10	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ in X in X = _); elpi z_report "pp.10" "24" ltac_term:(G)) | idtac "SSR	pp.10	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ in X in X /\ _); elpi z_report "pp.10" "25" ltac_term:(G)) | idtac "SSR	pp.10	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ as X in (X + _)%Z); elpi z_report "pp.10" "26" ltac_term:(G)) | idtac "SSR	pp.10	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (X + _)%Z = _); elpi z_report "pp.10" "27" ltac_term:(G)) | idtac "SSR	pp.10	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ in X in X = _ /\ _); elpi z_report "pp.10" "28" ltac_term:(G)) | idtac "SSR	pp.10	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ as X in (X + _)%Z = _); elpi z_report "pp.10" "29" ltac_term:(G)) | idtac "SSR	pp.10	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (X + _)%Z = _ /\ _); elpi z_report "pp.10" "30" ltac_term:(G)) | idtac "SSR	pp.10	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ as X in (X + _)%Z = _ /\ _); elpi z_report "pp.10" "31" ltac_term:(G)) | idtac "SSR	pp.10	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Z.of_nat n); elpi z_report "pp.10" "32" ltac_term:(G)) | idtac "SSR	pp.10	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Z.of_nat); elpi z_report "pp.10" "33" ltac_term:(G)) | idtac "SSR	pp.10	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Z.of_nat); elpi z_report "pp.10" "34" ltac_term:(G)) | idtac "SSR	pp.10	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Z.of_nat X); elpi z_report "pp.10" "35" ltac_term:(G)) | idtac "SSR	pp.10	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.10" "36" ltac_term:(G)) | idtac "SSR	pp.10	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.10" "37" ltac_term:(G)) | idtac "SSR	pp.10	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos _); elpi z_report "pp.10" "38" ltac_term:(G)) | idtac "SSR	pp.10	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ + X)%Z); elpi z_report "pp.10" "39" ltac_term:(G)) | idtac "SSR	pp.10	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos _ in X in X = _); elpi z_report "pp.10" "40" ltac_term:(G)) | idtac "SSR	pp.10	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos _ in X in X /\ _); elpi z_report "pp.10" "41" ltac_term:(G)) | idtac "SSR	pp.10	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos _ as X in (_ + X)%Z); elpi z_report "pp.10" "42" ltac_term:(G)) | idtac "SSR	pp.10	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ + X)%Z = _); elpi z_report "pp.10" "43" ltac_term:(G)) | idtac "SSR	pp.10	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos _ in X in X = _ /\ _); elpi z_report "pp.10" "44" ltac_term:(G)) | idtac "SSR	pp.10	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos _ as X in (_ + X)%Z = _); elpi z_report "pp.10" "45" ltac_term:(G)) | idtac "SSR	pp.10	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ + X)%Z = _ /\ _); elpi z_report "pp.10" "46" ltac_term:(G)) | idtac "SSR	pp.10	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos _ as X in (_ + X)%Z = _ /\ _); elpi z_report "pp.10" "47" ltac_term:(G)) | idtac "SSR	pp.10	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1%Z); elpi z_report "pp.10" "48" ltac_term:(G)) | idtac "SSR	pp.10	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.pos); elpi z_report "pp.10" "49" ltac_term:(G)) | idtac "SSR	pp.10	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Z.pos); elpi z_report "pp.10" "50" ltac_term:(G)) | idtac "SSR	pp.10	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1%positive); elpi z_report "pp.10" "51" ltac_term:(G)) | idtac "SSR	pp.10	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in Z.pos X); elpi z_report "pp.10" "52" ltac_term:(G)) | idtac "SSR	pp.10	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ + Z.pos X)%Z); elpi z_report "pp.10" "53" ltac_term:(G)) | idtac "SSR	pp.10	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ + Z.pos X)%Z = _); elpi z_report "pp.10" "54" ltac_term:(G)) | idtac "SSR	pp.10	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ + Z.pos X)%Z = _ /\ _); elpi z_report "pp.10" "55" ltac_term:(G)) | idtac "SSR	pp.10	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1%positive); elpi z_report "pp.10" "56" ltac_term:(G)) | idtac "SSR	pp.10	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.10" "57" ltac_term:(G)) | idtac "SSR	pp.10	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat b); elpi z_report "pp.10" "58" ltac_term:(G)) | idtac "SSR	pp.10	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ as X in _ = X); elpi z_report "pp.10" "59" ltac_term:(G)) | idtac "SSR	pp.10	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "pp.10" "60" ltac_term:(G)) | idtac "SSR	pp.10	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat b in X in X /\ _); elpi z_report "pp.10" "61" ltac_term:(G)) | idtac "SSR	pp.10	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat _ as X in _ = X /\ _); elpi z_report "pp.10" "62" ltac_term:(G)) | idtac "SSR	pp.10	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Z.of_nat b); elpi z_report "pp.10" "63" ltac_term:(G)) | idtac "SSR	pp.10	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Z.of_nat); elpi z_report "pp.10" "64" ltac_term:(G)) | idtac "SSR	pp.10	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Z.of_nat); elpi z_report "pp.10" "65" ltac_term:(G)) | idtac "SSR	pp.10	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Z.of_nat); elpi z_report "pp.10" "66" ltac_term:(G)) | idtac "SSR	pp.10	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ in X in _ = X); elpi z_report "pp.10" "67" ltac_term:(G)) | idtac "SSR	pp.10	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ in X in X /\ _); elpi z_report "pp.10" "68" ltac_term:(G)) | idtac "SSR	pp.10	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ as X in Z.of_nat X); elpi z_report "pp.10" "69" ltac_term:(G)) | idtac "SSR	pp.10	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ in X in _ = X /\ _); elpi z_report "pp.10" "70" ltac_term:(G)) | idtac "SSR	pp.10	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(unbox _); elpi z_report "pp.10" "71" ltac_term:(G)) | idtac "SSR	pp.10	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(unbox b); elpi z_report "pp.10" "72" ltac_term:(G)) | idtac "SSR	pp.10	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(unbox); elpi z_report "pp.10" "73" ltac_term:(G)) | idtac "SSR	pp.10	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(unbox); elpi z_report "pp.10" "74" ltac_term:(G)) | idtac "SSR	pp.10	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.10" "75" ltac_term:(G)) | idtac "SSR	pp.10	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.10" "76" ltac_term:(G)) | idtac "SSR	pp.10	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in unbox X); elpi z_report "pp.10" "77" ltac_term:(G)) | idtac "SSR	pp.10	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "pp.10" "78" ltac_term:(G)) | idtac "SSR	pp.10	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = n); elpi z_report "pp.10" "79" ltac_term:(G)) | idtac "SSR	pp.10	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "pp.10" "80" ltac_term:(G)) | idtac "SSR	pp.10	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b + 0 = n); elpi z_report "pp.10" "81" ltac_term:(G)) | idtac "SSR	pp.10	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.10" "82" ltac_term:(G)) | idtac "SSR	pp.10	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.10" "83" ltac_term:(G)) | idtac "SSR	pp.10	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.10" "84" ltac_term:(G)) | idtac "SSR	pp.10	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.10" "85" ltac_term:(G)) | idtac "SSR	pp.10	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.10" "86" ltac_term:(G)) | idtac "SSR	pp.10	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "pp.10" "87" ltac_term:(G)) | idtac "SSR	pp.10	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = n); elpi z_report "pp.10" "88" ltac_term:(G)) | idtac "SSR	pp.10	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "pp.10" "89" ltac_term:(G)) | idtac "SSR	pp.10	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ /\ X); elpi z_report "pp.10" "90" ltac_term:(G)) | idtac "SSR	pp.10	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "pp.10" "91" ltac_term:(G)) | idtac "SSR	pp.10	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ /\ X = _); elpi z_report "pp.10" "92" ltac_term:(G)) | idtac "SSR	pp.10	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b + 0); elpi z_report "pp.10" "93" ltac_term:(G)) | idtac "SSR	pp.10	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Init.Nat.add); elpi z_report "pp.10" "94" ltac_term:(G)) | idtac "SSR	pp.10	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Init.Nat.add); elpi z_report "pp.10" "95" ltac_term:(G)) | idtac "SSR	pp.10	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "pp.10" "96" ltac_term:(G)) | idtac "SSR	pp.10	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ as X in X + _); elpi z_report "pp.10" "97" ltac_term:(G)) | idtac "SSR	pp.10	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ in X in _ /\ X); elpi z_report "pp.10" "98" ltac_term:(G)) | idtac "SSR	pp.10	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "pp.10" "99" ltac_term:(G)) | idtac "SSR	pp.10	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ in X in X = n); elpi z_report "pp.10" "100" ltac_term:(G)) | idtac "SSR	pp.10	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ as X in X + _ = _); elpi z_report "pp.10" "101" ltac_term:(G)) | idtac "SSR	pp.10	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ in X in _ /\ X = _); elpi z_report "pp.10" "102" ltac_term:(G)) | idtac "SSR	pp.10	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X + _ = _); elpi z_report "pp.10" "103" ltac_term:(G)) | idtac "SSR	pp.10	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _ as X in _ /\ X + _ = _); elpi z_report "pp.10" "104" ltac_term:(G)) | idtac "SSR	pp.10	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox _); elpi z_report "pp.10" "105" ltac_term:(G)) | idtac "SSR	pp.10	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(unbox _); elpi z_report "pp.10" "106" ltac_term:(G)) | idtac "SSR	pp.10	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(unbox b); elpi z_report "pp.10" "107" ltac_term:(G)) | idtac "SSR	pp.10	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (unbox); elpi z_report "pp.10" "108" ltac_term:(G)) | idtac "SSR	pp.10	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(unbox); elpi z_report "pp.10" "109" ltac_term:(G)) | idtac "SSR	pp.10	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(unbox); elpi z_report "pp.10" "110" ltac_term:(G)) | idtac "SSR	pp.10	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.10" "111" ltac_term:(G)) | idtac "SSR	pp.10	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in unbox X); elpi z_report "pp.10" "112" ltac_term:(G)) | idtac "SSR	pp.10	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.10" "113" ltac_term:(G)) | idtac "SSR	pp.10	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.10" "114" ltac_term:(G)) | idtac "SSR	pp.10	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in unbox X); elpi z_report "pp.10" "115" ltac_term:(G)) | idtac "SSR	pp.10	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.10" "116" ltac_term:(G)) | idtac "SSR	pp.10	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "pp.10" "117" ltac_term:(G)) | idtac "SSR	pp.10	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "pp.10" "118" ltac_term:(G)) | idtac "SSR	pp.10	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ + X = _); elpi z_report "pp.10" "119" ltac_term:(G)) | idtac "SSR	pp.10	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.10" "120" ltac_term:(G)) | idtac "SSR	pp.10	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "pp.10" "121" ltac_term:(G)) | idtac "SSR	pp.10	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b + 0 = X); elpi z_report "pp.10" "122" ltac_term:(G)) | idtac "SSR	pp.10	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.10" "123" ltac_term:(G)) | idtac "SSR	pp.10	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.10" "124" ltac_term:(G)) | idtac "SSR	pp.10	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.10" "125" ltac_term:(G)) | idtac "SSR	pp.10	125	error" ].
Abort.
End C.

Set Printing All.
Goal forall a b : nat, a + b = b + a /\ (a <= b \/ True).
intros a b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "pp.11" "1" ltac_term:(G)) | idtac "SSR	pp.11	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b = b + a /\ (a <= b \/ True)); elpi z_report "pp.11" "2" ltac_term:(G)) | idtac "SSR	pp.11	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "pp.11" "3" ltac_term:(G)) | idtac "SSR	pp.11	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "pp.11" "4" ltac_term:(G)) | idtac "SSR	pp.11	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.11" "5" ltac_term:(G)) | idtac "SSR	pp.11	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "pp.11" "6" ltac_term:(G)) | idtac "SSR	pp.11	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "pp.11" "7" ltac_term:(G)) | idtac "SSR	pp.11	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b = b + a); elpi z_report "pp.11" "8" ltac_term:(G)) | idtac "SSR	pp.11	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.11" "9" ltac_term:(G)) | idtac "SSR	pp.11	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.11" "10" ltac_term:(G)) | idtac "SSR	pp.11	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.11" "11" ltac_term:(G)) | idtac "SSR	pp.11	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.11" "12" ltac_term:(G)) | idtac "SSR	pp.11	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "pp.11" "13" ltac_term:(G)) | idtac "SSR	pp.11	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.11" "14" ltac_term:(G)) | idtac "SSR	pp.11	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "pp.11" "15" ltac_term:(G)) | idtac "SSR	pp.11	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ _); elpi z_report "pp.11" "16" ltac_term:(G)) | idtac "SSR	pp.11	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "pp.11" "17" ltac_term:(G)) | idtac "SSR	pp.11	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _ /\ _); elpi z_report "pp.11" "18" ltac_term:(G)) | idtac "SSR	pp.11	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "pp.11" "19" ltac_term:(G)) | idtac "SSR	pp.11	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.11" "20" ltac_term:(G)) | idtac "SSR	pp.11	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.11" "21" ltac_term:(G)) | idtac "SSR	pp.11	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "pp.11" "22" ltac_term:(G)) | idtac "SSR	pp.11	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "pp.11" "23" ltac_term:(G)) | idtac "SSR	pp.11	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _ /\ _); elpi z_report "pp.11" "24" ltac_term:(G)) | idtac "SSR	pp.11	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.11" "25" ltac_term:(G)) | idtac "SSR	pp.11	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.11" "26" ltac_term:(G)) | idtac "SSR	pp.11	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "pp.11" "27" ltac_term:(G)) | idtac "SSR	pp.11	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "pp.11" "28" ltac_term:(G)) | idtac "SSR	pp.11	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _ /\ _); elpi z_report "pp.11" "29" ltac_term:(G)) | idtac "SSR	pp.11	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.11" "30" ltac_term:(G)) | idtac "SSR	pp.11	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.11" "31" ltac_term:(G)) | idtac "SSR	pp.11	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.11" "32" ltac_term:(G)) | idtac "SSR	pp.11	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _); elpi z_report "pp.11" "33" ltac_term:(G)) | idtac "SSR	pp.11	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "pp.11" "34" ltac_term:(G)) | idtac "SSR	pp.11	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "pp.11" "35" ltac_term:(G)) | idtac "SSR	pp.11	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _ in X in X /\ _); elpi z_report "pp.11" "36" ltac_term:(G)) | idtac "SSR	pp.11	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X /\ _); elpi z_report "pp.11" "37" ltac_term:(G)) | idtac "SSR	pp.11	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b + a); elpi z_report "pp.11" "38" ltac_term:(G)) | idtac "SSR	pp.11	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.11" "39" ltac_term:(G)) | idtac "SSR	pp.11	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "pp.11" "40" ltac_term:(G)) | idtac "SSR	pp.11	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "pp.11" "41" ltac_term:(G)) | idtac "SSR	pp.11	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + a); elpi z_report "pp.11" "42" ltac_term:(G)) | idtac "SSR	pp.11	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "pp.11" "43" ltac_term:(G)) | idtac "SSR	pp.11	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ /\ _); elpi z_report "pp.11" "44" ltac_term:(G)) | idtac "SSR	pp.11	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.11" "45" ltac_term:(G)) | idtac "SSR	pp.11	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.11" "46" ltac_term:(G)) | idtac "SSR	pp.11	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b + X); elpi z_report "pp.11" "47" ltac_term:(G)) | idtac "SSR	pp.11	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "pp.11" "48" ltac_term:(G)) | idtac "SSR	pp.11	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X /\ _); elpi z_report "pp.11" "49" ltac_term:(G)) | idtac "SSR	pp.11	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "pp.11" "50" ltac_term:(G)) | idtac "SSR	pp.11	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "pp.11" "51" ltac_term:(G)) | idtac "SSR	pp.11	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ \/ _); elpi z_report "pp.11" "52" ltac_term:(G)) | idtac "SSR	pp.11	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "pp.11" "53" ltac_term:(G)) | idtac "SSR	pp.11	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ \/ _ as X in _ /\ X); elpi z_report "pp.11" "54" ltac_term:(G)) | idtac "SSR	pp.11	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a <= b \/ True); elpi z_report "pp.11" "55" ltac_term:(G)) | idtac "SSR	pp.11	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (or); elpi z_report "pp.11" "56" ltac_term:(G)) | idtac "SSR	pp.11	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(or); elpi z_report "pp.11" "57" ltac_term:(G)) | idtac "SSR	pp.11	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ <= _); elpi z_report "pp.11" "58" ltac_term:(G)) | idtac "SSR	pp.11	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X \/ _); elpi z_report "pp.11" "59" ltac_term:(G)) | idtac "SSR	pp.11	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ <= _ as X in X \/ _); elpi z_report "pp.11" "60" ltac_term:(G)) | idtac "SSR	pp.11	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ <= _ in X in _ /\ X); elpi z_report "pp.11" "61" ltac_term:(G)) | idtac "SSR	pp.11	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ (X \/ _)); elpi z_report "pp.11" "62" ltac_term:(G)) | idtac "SSR	pp.11	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ <= _ as X in _ /\ (X \/ _)); elpi z_report "pp.11" "63" ltac_term:(G)) | idtac "SSR	pp.11	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a <= b); elpi z_report "pp.11" "64" ltac_term:(G)) | idtac "SSR	pp.11	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (le); elpi z_report "pp.11" "65" ltac_term:(G)) | idtac "SSR	pp.11	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(le); elpi z_report "pp.11" "66" ltac_term:(G)) | idtac "SSR	pp.11	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X <= _); elpi z_report "pp.11" "67" ltac_term:(G)) | idtac "SSR	pp.11	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X <= _ \/ _); elpi z_report "pp.11" "68" ltac_term:(G)) | idtac "SSR	pp.11	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ (X <= _ \/ _)); elpi z_report "pp.11" "69" ltac_term:(G)) | idtac "SSR	pp.11	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "pp.11" "70" ltac_term:(G)) | idtac "SSR	pp.11	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "pp.11" "71" ltac_term:(G)) | idtac "SSR	pp.11	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "pp.11" "72" ltac_term:(G)) | idtac "SSR	pp.11	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ <= X); elpi z_report "pp.11" "73" ltac_term:(G)) | idtac "SSR	pp.11	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ <= X \/ _); elpi z_report "pp.11" "74" ltac_term:(G)) | idtac "SSR	pp.11	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ (_ <= X \/ _)); elpi z_report "pp.11" "75" ltac_term:(G)) | idtac "SSR	pp.11	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.11" "76" ltac_term:(G)) | idtac "SSR	pp.11	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "pp.11" "77" ltac_term:(G)) | idtac "SSR	pp.11	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "pp.11" "78" ltac_term:(G)) | idtac "SSR	pp.11	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (True); elpi z_report "pp.11" "79" ltac_term:(G)) | idtac "SSR	pp.11	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ \/ X); elpi z_report "pp.11" "80" ltac_term:(G)) | idtac "SSR	pp.11	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ (_ \/ X)); elpi z_report "pp.11" "81" ltac_term:(G)) | idtac "SSR	pp.11	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(True); elpi z_report "pp.11" "82" ltac_term:(G)) | idtac "SSR	pp.11	82	error" ].
Abort.
Unset Printing All.

Goal forall n : nat, n = n.
intros n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.12" "1" ltac_term:(G)) | idtac "SSR	pp.12	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n = n); elpi z_report "pp.12" "2" ltac_term:(G)) | idtac "SSR	pp.12	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.12" "3" ltac_term:(G)) | idtac "SSR	pp.12	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.12" "4" ltac_term:(G)) | idtac "SSR	pp.12	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.12" "5" ltac_term:(G)) | idtac "SSR	pp.12	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.12" "6" ltac_term:(G)) | idtac "SSR	pp.12	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.12" "7" ltac_term:(G)) | idtac "SSR	pp.12	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.12" "8" ltac_term:(G)) | idtac "SSR	pp.12	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.12" "9" ltac_term:(G)) | idtac "SSR	pp.12	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.12" "10" ltac_term:(G)) | idtac "SSR	pp.12	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.12" "11" ltac_term:(G)) | idtac "SSR	pp.12	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.12" "12" ltac_term:(G)) | idtac "SSR	pp.12	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.12" "13" ltac_term:(G)) | idtac "SSR	pp.12	13	error" ].
Abort.

Module IfMatch.
Notation "'IF' c 'THEN' a 'ELSE' b" := (if c then a else b) (at level 200).
Goal forall (b : bool) (n : nat), (IF b THEN n ELSE 0) = n.
intros b n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.13" "1" ltac_term:(G)) | idtac "SSR	pp.13	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((if b then n else 0) = n); elpi z_report "pp.13" "2" ltac_term:(G)) | idtac "SSR	pp.13	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.13" "3" ltac_term:(G)) | idtac "SSR	pp.13	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.13" "4" ltac_term:(G)) | idtac "SSR	pp.13	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.13" "5" ltac_term:(G)) | idtac "SSR	pp.13	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.13" "6" ltac_term:(G)) | idtac "SSR	pp.13	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.13" "7" ltac_term:(G)) | idtac "SSR	pp.13	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (if b then n else 0); elpi z_report "pp.13" "8" ltac_term:(G)) | idtac "SSR	pp.13	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(if b then n else 0); elpi z_report "pp.13" "9" ltac_term:(G)) | idtac "SSR	pp.13	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.13" "10" ltac_term:(G)) | idtac "SSR	pp.13	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.13" "11" ltac_term:(G)) | idtac "SSR	pp.13	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.13" "12" ltac_term:(G)) | idtac "SSR	pp.13	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.13" "13" ltac_term:(G)) | idtac "SSR	pp.13	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.13" "14" ltac_term:(G)) | idtac "SSR	pp.13	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.13" "15" ltac_term:(G)) | idtac "SSR	pp.13	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.13" "16" ltac_term:(G)) | idtac "SSR	pp.13	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.13" "17" ltac_term:(G)) | idtac "SSR	pp.13	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.13" "18" ltac_term:(G)) | idtac "SSR	pp.13	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.13" "19" ltac_term:(G)) | idtac "SSR	pp.13	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.13" "20" ltac_term:(G)) | idtac "SSR	pp.13	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.13" "21" ltac_term:(G)) | idtac "SSR	pp.13	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.13" "22" ltac_term:(G)) | idtac "SSR	pp.13	22	error" ].
Abort.
End IfMatch.

Goal forall (b : bool) (n : nat), (if b then n else 0) = n.
intros b n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.14" "1" ltac_term:(G)) | idtac "SSR	pp.14	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((if b then n else 0) = n); elpi z_report "pp.14" "2" ltac_term:(G)) | idtac "SSR	pp.14	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.14" "3" ltac_term:(G)) | idtac "SSR	pp.14	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.14" "4" ltac_term:(G)) | idtac "SSR	pp.14	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.14" "5" ltac_term:(G)) | idtac "SSR	pp.14	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.14" "6" ltac_term:(G)) | idtac "SSR	pp.14	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.14" "7" ltac_term:(G)) | idtac "SSR	pp.14	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (if b then n else 0); elpi z_report "pp.14" "8" ltac_term:(G)) | idtac "SSR	pp.14	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(if b then n else 0); elpi z_report "pp.14" "9" ltac_term:(G)) | idtac "SSR	pp.14	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.14" "10" ltac_term:(G)) | idtac "SSR	pp.14	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.14" "11" ltac_term:(G)) | idtac "SSR	pp.14	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.14" "12" ltac_term:(G)) | idtac "SSR	pp.14	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.14" "13" ltac_term:(G)) | idtac "SSR	pp.14	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.14" "14" ltac_term:(G)) | idtac "SSR	pp.14	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.14" "15" ltac_term:(G)) | idtac "SSR	pp.14	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.14" "16" ltac_term:(G)) | idtac "SSR	pp.14	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.14" "17" ltac_term:(G)) | idtac "SSR	pp.14	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.14" "18" ltac_term:(G)) | idtac "SSR	pp.14	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.14" "19" ltac_term:(G)) | idtac "SSR	pp.14	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.14" "20" ltac_term:(G)) | idtac "SSR	pp.14	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.14" "21" ltac_term:(G)) | idtac "SSR	pp.14	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.14" "22" ltac_term:(G)) | idtac "SSR	pp.14	22	error" ].
Abort.

Goal forall n : nat, match n with 0 => true | S _ => false end = true.
intros n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.15" "1" ltac_term:(G)) | idtac "SSR	pp.15	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(match n with | 0 => true | S _ => false end = true); elpi z_report "pp.15" "2" ltac_term:(G)) | idtac "SSR	pp.15	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.15" "3" ltac_term:(G)) | idtac "SSR	pp.15	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.15" "4" ltac_term:(G)) | idtac "SSR	pp.15	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.15" "5" ltac_term:(G)) | idtac "SSR	pp.15	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(bool); elpi z_report "pp.15" "6" ltac_term:(G)) | idtac "SSR	pp.15	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.15" "7" ltac_term:(G)) | idtac "SSR	pp.15	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (match n with | 0 => true | S _ => false end); elpi z_report "pp.15" "8" ltac_term:(G)) | idtac "SSR	pp.15	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(match n with | 0 => true | S _ => false end); elpi z_report "pp.15" "9" ltac_term:(G)) | idtac "SSR	pp.15	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.15" "10" ltac_term:(G)) | idtac "SSR	pp.15	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.15" "11" ltac_term:(G)) | idtac "SSR	pp.15	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (bool); elpi z_report "pp.15" "12" ltac_term:(G)) | idtac "SSR	pp.15	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.15" "13" ltac_term:(G)) | idtac "SSR	pp.15	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(bool); elpi z_report "pp.15" "14" ltac_term:(G)) | idtac "SSR	pp.15	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.15" "15" ltac_term:(G)) | idtac "SSR	pp.15	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.15" "16" ltac_term:(G)) | idtac "SSR	pp.15	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (false); elpi z_report "pp.15" "17" ltac_term:(G)) | idtac "SSR	pp.15	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(false); elpi z_report "pp.15" "18" ltac_term:(G)) | idtac "SSR	pp.15	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.15" "19" ltac_term:(G)) | idtac "SSR	pp.15	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (true); elpi z_report "pp.15" "20" ltac_term:(G)) | idtac "SSR	pp.15	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.15" "21" ltac_term:(G)) | idtac "SSR	pp.15	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(true); elpi z_report "pp.15" "22" ltac_term:(G)) | idtac "SSR	pp.15	22	error" ].
Abort.

Goal forall n : nat, n + 0 = n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (forall n : nat, n + 0 = n); elpi z_report "pp.16" "1" ltac_term:(G)) | idtac "SSR	pp.16	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(forall n : nat, n + 0 = n); elpi z_report "pp.16" "2" ltac_term:(G)) | idtac "SSR	pp.16	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.16" "3" ltac_term:(G)) | idtac "SSR	pp.16	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.16" "4" ltac_term:(G)) | idtac "SSR	pp.16	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.16" "5" ltac_term:(G)) | idtac "SSR	pp.16	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.16" "6" ltac_term:(G)) | idtac "SSR	pp.16	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.16" "7" ltac_term:(G)) | idtac "SSR	pp.16	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.16" "8" ltac_term:(G)) | idtac "SSR	pp.16	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.16" "9" ltac_term:(G)) | idtac "SSR	pp.16	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.16" "10" ltac_term:(G)) | idtac "SSR	pp.16	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.16" "11" ltac_term:(G)) | idtac "SSR	pp.16	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.16" "12" ltac_term:(G)) | idtac "SSR	pp.16	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.16" "13" ltac_term:(G)) | idtac "SSR	pp.16	13	error" ].
Abort.

Goal forall n : nat, (let m := n + 1 in m * m) = n /\ (fun k : nat => k) n = n.
intros n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "pp.17" "1" ltac_term:(G)) | idtac "SSR	pp.17	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((let m := n + 1 in m * m) = n /\ [k : nat in k] n = n); elpi z_report "pp.17" "2" ltac_term:(G)) | idtac "SSR	pp.17	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "pp.17" "3" ltac_term:(G)) | idtac "SSR	pp.17	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "pp.17" "4" ltac_term:(G)) | idtac "SSR	pp.17	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.17" "5" ltac_term:(G)) | idtac "SSR	pp.17	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "pp.17" "6" ltac_term:(G)) | idtac "SSR	pp.17	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "pp.17" "7" ltac_term:(G)) | idtac "SSR	pp.17	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((let m := n + 1 in m * m) = n); elpi z_report "pp.17" "8" ltac_term:(G)) | idtac "SSR	pp.17	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.17" "9" ltac_term:(G)) | idtac "SSR	pp.17	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.17" "10" ltac_term:(G)) | idtac "SSR	pp.17	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.17" "11" ltac_term:(G)) | idtac "SSR	pp.17	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.17" "12" ltac_term:(G)) | idtac "SSR	pp.17	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.17" "13" ltac_term:(G)) | idtac "SSR	pp.17	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "pp.17" "14" ltac_term:(G)) | idtac "SSR	pp.17	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.17" "15" ltac_term:(G)) | idtac "SSR	pp.17	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.17" "16" ltac_term:(G)) | idtac "SSR	pp.17	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "pp.17" "17" ltac_term:(G)) | idtac "SSR	pp.17	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X = _); elpi z_report "pp.17" "18" ltac_term:(G)) | idtac "SSR	pp.17	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ _); elpi z_report "pp.17" "19" ltac_term:(G)) | idtac "SSR	pp.17	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X = _ /\ _); elpi z_report "pp.17" "20" ltac_term:(G)) | idtac "SSR	pp.17	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n + 1); elpi z_report "pp.17" "21" ltac_term:(G)) | idtac "SSR	pp.17	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.17" "22" ltac_term:(G)) | idtac "SSR	pp.17	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.17" "23" ltac_term:(G)) | idtac "SSR	pp.17	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "pp.17" "24" ltac_term:(G)) | idtac "SSR	pp.17	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.17" "25" ltac_term:(G)) | idtac "SSR	pp.17	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "pp.17" "26" ltac_term:(G)) | idtac "SSR	pp.17	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "pp.17" "27" ltac_term:(G)) | idtac "SSR	pp.17	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "pp.17" "28" ltac_term:(G)) | idtac "SSR	pp.17	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X); elpi z_report "pp.17" "29" ltac_term:(G)) | idtac "SSR	pp.17	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "pp.17" "30" ltac_term:(G)) | idtac "SSR	pp.17	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X /\ _); elpi z_report "pp.17" "31" ltac_term:(G)) | idtac "SSR	pp.17	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _ /\ _); elpi z_report "pp.17" "32" ltac_term:(G)) | idtac "SSR	pp.17	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "pp.17" "33" ltac_term:(G)) | idtac "SSR	pp.17	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "pp.17" "34" ltac_term:(G)) | idtac "SSR	pp.17	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.17" "35" ltac_term:(G)) | idtac "SSR	pp.17	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.17" "36" ltac_term:(G)) | idtac "SSR	pp.17	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "pp.17" "37" ltac_term:(G)) | idtac "SSR	pp.17	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X); elpi z_report "pp.17" "38" ltac_term:(G)) | idtac "SSR	pp.17	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.17" "39" ltac_term:(G)) | idtac "SSR	pp.17	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.mul); elpi z_report "pp.17" "40" ltac_term:(G)) | idtac "SSR	pp.17	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.mul); elpi z_report "pp.17" "41" ltac_term:(G)) | idtac "SSR	pp.17	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "pp.17" "42" ltac_term:(G)) | idtac "SSR	pp.17	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.17" "43" ltac_term:(G)) | idtac "SSR	pp.17	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "pp.17" "44" ltac_term:(G)) | idtac "SSR	pp.17	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "pp.17" "45" ltac_term:(G)) | idtac "SSR	pp.17	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in _ /\ X); elpi z_report "pp.17" "46" ltac_term:(G)) | idtac "SSR	pp.17	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ([k : nat in k] n = _); elpi z_report "pp.17" "47" ltac_term:(G)) | idtac "SSR	pp.17	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}([k : nat in k] n = n); elpi z_report "pp.17" "48" ltac_term:(G)) | idtac "SSR	pp.17	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.17" "49" ltac_term:(G)) | idtac "SSR	pp.17	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.17" "50" ltac_term:(G)) | idtac "SSR	pp.17	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.17" "51" ltac_term:(G)) | idtac "SSR	pp.17	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.17" "52" ltac_term:(G)) | idtac "SSR	pp.17	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.17" "53" ltac_term:(G)) | idtac "SSR	pp.17	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X = _); elpi z_report "pp.17" "54" ltac_term:(G)) | idtac "SSR	pp.17	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.17" "55" ltac_term:(G)) | idtac "SSR	pp.17	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "pp.17" "56" ltac_term:(G)) | idtac "SSR	pp.17	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(nat); elpi z_report "pp.17" "57" ltac_term:(G)) | idtac "SSR	pp.17	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ [k : nat in k] X = _); elpi z_report "pp.17" "58" ltac_term:(G)) | idtac "SSR	pp.17	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "pp.17" "59" ltac_term:(G)) | idtac "SSR	pp.17	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(n); elpi z_report "pp.17" "60" ltac_term:(G)) | idtac "SSR	pp.17	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ _ = X); elpi z_report "pp.17" "61" ltac_term:(G)) | idtac "SSR	pp.17	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in [k : nat in k] n = X); elpi z_report "pp.17" "62" ltac_term:(G)) | idtac "SSR	pp.17	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "pp.17" "63" ltac_term:(G)) | idtac "SSR	pp.17	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "pp.17" "64" ltac_term:(G)) | idtac "SSR	pp.17	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(n); elpi z_report "pp.17" "65" ltac_term:(G)) | idtac "SSR	pp.17	65	error" ].
Abort.

Goal forall (n : nat), match n with 0 => true | S k => Nat.eqb k n end = true -> (forall z : nat, z = z) -> True.
intros n H H'.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (True); elpi z_report "pp.18" "1" ltac_term:(G)) | idtac "SSR	pp.18	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(True); elpi z_report "pp.18" "2" ltac_term:(G)) | idtac "SSR	pp.18	2	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := (forall z : nat, z = z) in H'; elpi z_report "pp.18" "3" ltac_term:(G) "H'") | idtac "SSR	pp.18	3	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := {1}(forall z : nat, z = z) in H'; elpi z_report "pp.18" "4" ltac_term:(G) "H'") | idtac "SSR	pp.18	4	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H'; elpi z_report "pp.18" "5" ltac_term:(G) "H'") | idtac "SSR	pp.18	5	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H'; elpi z_report "pp.18" "6" ltac_term:(G) "H'") | idtac "SSR	pp.18	6	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := (@eq) in H'; elpi z_report "pp.18" "7" ltac_term:(G) "H'") | idtac "SSR	pp.18	7	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H'; elpi z_report "pp.18" "8" ltac_term:(G) "H'") | idtac "SSR	pp.18	8	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := (nat) in H'; elpi z_report "pp.18" "9" ltac_term:(G) "H'") | idtac "SSR	pp.18	9	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H'; elpi z_report "pp.18" "10" ltac_term:(G) "H'") | idtac "SSR	pp.18	10	error" ].
let G := type of H' in first [ assert_succeeds (set pattern_select_z := {2}(nat) in H'; elpi z_report "pp.18" "11" ltac_term:(G) "H'") | idtac "SSR	pp.18	11	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ = _) in H; elpi z_report "pp.18" "12" ltac_term:(G) "H") | idtac "SSR	pp.18	12	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(match n with | 0 => true | S k => Nat.eqb k n end = true) in H; elpi z_report "pp.18" "13" ltac_term:(G) "H") | idtac "SSR	pp.18	13	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (@eq) in H; elpi z_report "pp.18" "14" ltac_term:(G) "H") | idtac "SSR	pp.18	14	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H; elpi z_report "pp.18" "15" ltac_term:(G) "H") | idtac "SSR	pp.18	15	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(bool) in H; elpi z_report "pp.18" "16" ltac_term:(G) "H") | idtac "SSR	pp.18	16	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(bool) in H; elpi z_report "pp.18" "17" ltac_term:(G) "H") | idtac "SSR	pp.18	17	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in X = _) in H; elpi z_report "pp.18" "18" ltac_term:(G) "H") | idtac "SSR	pp.18	18	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (match n with | 0 => true | S k => Nat.eqb k n end) in H; elpi z_report "pp.18" "19" ltac_term:(G) "H") | idtac "SSR	pp.18	19	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(match n with | 0 => true | S k => Nat.eqb k n end) in H; elpi z_report "pp.18" "20" ltac_term:(G) "H") | idtac "SSR	pp.18	20	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(n) in H; elpi z_report "pp.18" "21" ltac_term:(G) "H") | idtac "SSR	pp.18	21	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(n) in H; elpi z_report "pp.18" "22" ltac_term:(G) "H") | idtac "SSR	pp.18	22	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (bool) in H; elpi z_report "pp.18" "23" ltac_term:(G) "H") | idtac "SSR	pp.18	23	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(bool) in H; elpi z_report "pp.18" "24" ltac_term:(G) "H") | idtac "SSR	pp.18	24	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(bool) in H; elpi z_report "pp.18" "25" ltac_term:(G) "H") | idtac "SSR	pp.18	25	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(true) in H; elpi z_report "pp.18" "26" ltac_term:(G) "H") | idtac "SSR	pp.18	26	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(true) in H; elpi z_report "pp.18" "27" ltac_term:(G) "H") | idtac "SSR	pp.18	27	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (Nat.eqb) in H; elpi z_report "pp.18" "28" ltac_term:(G) "H") | idtac "SSR	pp.18	28	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(Nat.eqb) in H; elpi z_report "pp.18" "29" ltac_term:(G) "H") | idtac "SSR	pp.18	29	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (n) in H; elpi z_report "pp.18" "30" ltac_term:(G) "H") | idtac "SSR	pp.18	30	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(n) in H; elpi z_report "pp.18" "31" ltac_term:(G) "H") | idtac "SSR	pp.18	31	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(n) in H; elpi z_report "pp.18" "32" ltac_term:(G) "H") | idtac "SSR	pp.18	32	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = X) in H; elpi z_report "pp.18" "33" ltac_term:(G) "H") | idtac "SSR	pp.18	33	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (true) in H; elpi z_report "pp.18" "34" ltac_term:(G) "H") | idtac "SSR	pp.18	34	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(true) in H; elpi z_report "pp.18" "35" ltac_term:(G) "H") | idtac "SSR	pp.18	35	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(true) in H; elpi z_report "pp.18" "36" ltac_term:(G) "H") | idtac "SSR	pp.18	36	error" ].
Abort.

Lemma two_is : 2 = 1 + 1. Proof. reflexivity. Qed.
Goal forall a : nat, double (1 + a) = 2 + a + a -> forall n : nat, n + double a = a.
intros a H.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (forall n : nat, n + double a = a); elpi z_report "pp.19" "1" ltac_term:(G)) | idtac "SSR	pp.19	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(forall n : nat, n + double a = a); elpi z_report "pp.19" "2" ltac_term:(G)) | idtac "SSR	pp.19	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.19" "3" ltac_term:(G)) | idtac "SSR	pp.19	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.19" "4" ltac_term:(G)) | idtac "SSR	pp.19	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.19" "5" ltac_term:(G)) | idtac "SSR	pp.19	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.19" "6" ltac_term:(G)) | idtac "SSR	pp.19	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.19" "7" ltac_term:(G)) | idtac "SSR	pp.19	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.19" "8" ltac_term:(G)) | idtac "SSR	pp.19	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.19" "9" ltac_term:(G)) | idtac "SSR	pp.19	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.19" "10" ltac_term:(G)) | idtac "SSR	pp.19	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.19" "11" ltac_term:(G)) | idtac "SSR	pp.19	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double _); elpi z_report "pp.19" "12" ltac_term:(G)) | idtac "SSR	pp.19	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(double a); elpi z_report "pp.19" "13" ltac_term:(G)) | idtac "SSR	pp.19	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double); elpi z_report "pp.19" "14" ltac_term:(G)) | idtac "SSR	pp.19	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(double); elpi z_report "pp.19" "15" ltac_term:(G)) | idtac "SSR	pp.19	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double X); elpi z_report "pp.19" "16" ltac_term:(G)) | idtac "SSR	pp.19	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.19" "17" ltac_term:(G)) | idtac "SSR	pp.19	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.19" "18" ltac_term:(G)) | idtac "SSR	pp.19	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "pp.19" "19" ltac_term:(G)) | idtac "SSR	pp.19	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "pp.19" "20" ltac_term:(G)) | idtac "SSR	pp.19	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "pp.19" "21" ltac_term:(G)) | idtac "SSR	pp.19	21	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ = _) in H; elpi z_report "pp.19" "22" ltac_term:(G) "H") | idtac "SSR	pp.19	22	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(double (1 + a) = 2 + a + a) in H; elpi z_report "pp.19" "23" ltac_term:(G) "H") | idtac "SSR	pp.19	23	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (@eq) in H; elpi z_report "pp.19" "24" ltac_term:(G) "H") | idtac "SSR	pp.19	24	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(@eq) in H; elpi z_report "pp.19" "25" ltac_term:(G) "H") | idtac "SSR	pp.19	25	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (nat) in H; elpi z_report "pp.19" "26" ltac_term:(G) "H") | idtac "SSR	pp.19	26	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(nat) in H; elpi z_report "pp.19" "27" ltac_term:(G) "H") | idtac "SSR	pp.19	27	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (double _) in H; elpi z_report "pp.19" "28" ltac_term:(G) "H") | idtac "SSR	pp.19	28	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in X = _) in H; elpi z_report "pp.19" "29" ltac_term:(G) "H") | idtac "SSR	pp.19	29	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (double _ as X in X = _) in H; elpi z_report "pp.19" "30" ltac_term:(G) "H") | idtac "SSR	pp.19	30	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(double (1 + a)) in H; elpi z_report "pp.19" "31" ltac_term:(G) "H") | idtac "SSR	pp.19	31	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (double) in H; elpi z_report "pp.19" "32" ltac_term:(G) "H") | idtac "SSR	pp.19	32	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(double) in H; elpi z_report "pp.19" "33" ltac_term:(G) "H") | idtac "SSR	pp.19	33	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + _) in H; elpi z_report "pp.19" "34" ltac_term:(G) "H") | idtac "SSR	pp.19	34	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double X) in H; elpi z_report "pp.19" "35" ltac_term:(G) "H") | idtac "SSR	pp.19	35	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X = _) in H; elpi z_report "pp.19" "36" ltac_term:(G) "H") | idtac "SSR	pp.19	36	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in double X) in H; elpi z_report "pp.19" "37" ltac_term:(G) "H") | idtac "SSR	pp.19	37	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double X = _) in H; elpi z_report "pp.19" "38" ltac_term:(G) "H") | idtac "SSR	pp.19	38	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in double X = _) in H; elpi z_report "pp.19" "39" ltac_term:(G) "H") | idtac "SSR	pp.19	39	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(1 + a) in H; elpi z_report "pp.19" "40" ltac_term:(G) "H") | idtac "SSR	pp.19	40	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H; elpi z_report "pp.19" "41" ltac_term:(G) "H") | idtac "SSR	pp.19	41	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add) in H; elpi z_report "pp.19" "42" ltac_term:(G) "H") | idtac "SSR	pp.19	42	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in X + _) in H; elpi z_report "pp.19" "43" ltac_term:(G) "H") | idtac "SSR	pp.19	43	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _) in H; elpi z_report "pp.19" "44" ltac_term:(G) "H") | idtac "SSR	pp.19	44	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _) in H; elpi z_report "pp.19" "45" ltac_term:(G) "H") | idtac "SSR	pp.19	45	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ in X in double X) in H; elpi z_report "pp.19" "46" ltac_term:(G) "H") | idtac "SSR	pp.19	46	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double (X + _)) in H; elpi z_report "pp.19" "47" ltac_term:(G) "H") | idtac "SSR	pp.19	47	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ in X in double X = _) in H; elpi z_report "pp.19" "48" ltac_term:(G) "H") | idtac "SSR	pp.19	48	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in double (X + _)) in H; elpi z_report "pp.19" "49" ltac_term:(G) "H") | idtac "SSR	pp.19	49	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double (X + _) = _) in H; elpi z_report "pp.19" "50" ltac_term:(G) "H") | idtac "SSR	pp.19	50	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in double (X + _) = _) in H; elpi z_report "pp.19" "51" ltac_term:(G) "H") | idtac "SSR	pp.19	51	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _) in H; elpi z_report "pp.19" "52" ltac_term:(G) "H") | idtac "SSR	pp.19	52	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(1) in H; elpi z_report "pp.19" "53" ltac_term:(G) "H") | idtac "SSR	pp.19	53	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(S _) in H; elpi z_report "pp.19" "54" ltac_term:(G) "H") | idtac "SSR	pp.19	54	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(S) in H; elpi z_report "pp.19" "55" ltac_term:(G) "H") | idtac "SSR	pp.19	55	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(S) in H; elpi z_report "pp.19" "56" ltac_term:(G) "H") | idtac "SSR	pp.19	56	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in S X + _) in H; elpi z_report "pp.19" "57" ltac_term:(G) "H") | idtac "SSR	pp.19	57	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double (S X + _)) in H; elpi z_report "pp.19" "58" ltac_term:(G) "H") | idtac "SSR	pp.19	58	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double (S X + _) = _) in H; elpi z_report "pp.19" "59" ltac_term:(G) "H") | idtac "SSR	pp.19	59	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in S X) in H; elpi z_report "pp.19" "60" ltac_term:(G) "H") | idtac "SSR	pp.19	60	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(0) in H; elpi z_report "pp.19" "61" ltac_term:(G) "H") | idtac "SSR	pp.19	61	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(0) in H; elpi z_report "pp.19" "62" ltac_term:(G) "H") | idtac "SSR	pp.19	62	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(X in S X) in H; elpi z_report "pp.19" "63" ltac_term:(G) "H") | idtac "SSR	pp.19	63	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ + X) in H; elpi z_report "pp.19" "64" ltac_term:(G) "H") | idtac "SSR	pp.19	64	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double (_ + X)) in H; elpi z_report "pp.19" "65" ltac_term:(G) "H") | idtac "SSR	pp.19	65	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in double (_ + X) = _) in H; elpi z_report "pp.19" "66" ltac_term:(G) "H") | idtac "SSR	pp.19	66	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(a) in H; elpi z_report "pp.19" "67" ltac_term:(G) "H") | idtac "SSR	pp.19	67	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(a) in H; elpi z_report "pp.19" "68" ltac_term:(G) "H") | idtac "SSR	pp.19	68	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = X) in H; elpi z_report "pp.19" "69" ltac_term:(G) "H") | idtac "SSR	pp.19	69	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X) in H; elpi z_report "pp.19" "70" ltac_term:(G) "H") | idtac "SSR	pp.19	70	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (2 + a + _) in H; elpi z_report "pp.19" "71" ltac_term:(G) "H") | idtac "SSR	pp.19	71	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(2 + a + a) in H; elpi z_report "pp.19" "72" ltac_term:(G) "H") | idtac "SSR	pp.19	72	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add) in H; elpi z_report "pp.19" "73" ltac_term:(G) "H") | idtac "SSR	pp.19	73	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add) in H; elpi z_report "pp.19" "74" ltac_term:(G) "H") | idtac "SSR	pp.19	74	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (2 + _) in H; elpi z_report "pp.19" "75" ltac_term:(G) "H") | idtac "SSR	pp.19	75	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _) in H; elpi z_report "pp.19" "76" ltac_term:(G) "H") | idtac "SSR	pp.19	76	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _) in H; elpi z_report "pp.19" "77" ltac_term:(G) "H") | idtac "SSR	pp.19	77	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (2 + _ in X in _ = X) in H; elpi z_report "pp.19" "78" ltac_term:(G) "H") | idtac "SSR	pp.19	78	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X + _) in H; elpi z_report "pp.19" "79" ltac_term:(G) "H") | idtac "SSR	pp.19	79	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(2 + a) in H; elpi z_report "pp.19" "80" ltac_term:(G) "H") | idtac "SSR	pp.19	80	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (Nat.add) in H; elpi z_report "pp.19" "81" ltac_term:(G) "H") | idtac "SSR	pp.19	81	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add) in H; elpi z_report "pp.19" "82" ltac_term:(G) "H") | idtac "SSR	pp.19	82	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add) in H; elpi z_report "pp.19" "83" ltac_term:(G) "H") | idtac "SSR	pp.19	83	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (2) in H; elpi z_report "pp.19" "84" ltac_term:(G) "H") | idtac "SSR	pp.19	84	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (2 as X in X + _) in H; elpi z_report "pp.19" "85" ltac_term:(G) "H") | idtac "SSR	pp.19	85	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X) in H; elpi z_report "pp.19" "86" ltac_term:(G) "H") | idtac "SSR	pp.19	86	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _) in H; elpi z_report "pp.19" "87" ltac_term:(G) "H") | idtac "SSR	pp.19	87	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ + _) in H; elpi z_report "pp.19" "88" ltac_term:(G) "H") | idtac "SSR	pp.19	88	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X + _) in H; elpi z_report "pp.19" "89" ltac_term:(G) "H") | idtac "SSR	pp.19	89	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ + _) in H; elpi z_report "pp.19" "90" ltac_term:(G) "H") | idtac "SSR	pp.19	90	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X + _ + _) in H; elpi z_report "pp.19" "91" ltac_term:(G) "H") | idtac "SSR	pp.19	91	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {1}(2) in H; elpi z_report "pp.19" "92" ltac_term:(G) "H") | idtac "SSR	pp.19	92	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(S) in H; elpi z_report "pp.19" "93" ltac_term:(G) "H") | idtac "SSR	pp.19	93	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(S) in H; elpi z_report "pp.19" "94" ltac_term:(G) "H") | idtac "SSR	pp.19	94	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X) in H; elpi z_report "pp.19" "95" ltac_term:(G) "H") | idtac "SSR	pp.19	95	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (1 in X in _ = X) in H; elpi z_report "pp.19" "96" ltac_term:(G) "H") | idtac "SSR	pp.19	96	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X + _) in H; elpi z_report "pp.19" "97" ltac_term:(G) "H") | idtac "SSR	pp.19	97	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (1 in X in _ = X + _) in H; elpi z_report "pp.19" "98" ltac_term:(G) "H") | idtac "SSR	pp.19	98	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (1 in X in X + _ + _) in H; elpi z_report "pp.19" "99" ltac_term:(G) "H") | idtac "SSR	pp.19	99	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in S X + _ + _) in H; elpi z_report "pp.19" "100" ltac_term:(G) "H") | idtac "SSR	pp.19	100	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X + _ + _) in H; elpi z_report "pp.19" "101" ltac_term:(G) "H") | idtac "SSR	pp.19	101	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = S X + _ + _) in H; elpi z_report "pp.19" "102" ltac_term:(G) "H") | idtac "SSR	pp.19	102	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = S X + _ + _) in H; elpi z_report "pp.19" "103" ltac_term:(G) "H") | idtac "SSR	pp.19	103	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (1) in H; elpi z_report "pp.19" "104" ltac_term:(G) "H") | idtac "SSR	pp.19	104	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(1) in H; elpi z_report "pp.19" "105" ltac_term:(G) "H") | idtac "SSR	pp.19	105	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(1) in H; elpi z_report "pp.19" "106" ltac_term:(G) "H") | idtac "SSR	pp.19	106	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (S) in H; elpi z_report "pp.19" "107" ltac_term:(G) "H") | idtac "SSR	pp.19	107	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {3}(S) in H; elpi z_report "pp.19" "108" ltac_term:(G) "H") | idtac "SSR	pp.19	108	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {3}(S) in H; elpi z_report "pp.19" "109" ltac_term:(G) "H") | idtac "SSR	pp.19	109	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in S (S X)) in H; elpi z_report "pp.19" "110" ltac_term:(G) "H") | idtac "SSR	pp.19	110	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in S (S X) + _) in H; elpi z_report "pp.19" "111" ltac_term:(G) "H") | idtac "SSR	pp.19	111	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in S (S X) + _ + _) in H; elpi z_report "pp.19" "112" ltac_term:(G) "H") | idtac "SSR	pp.19	112	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = S (S X) + _ + _) in H; elpi z_report "pp.19" "113" ltac_term:(G) "H") | idtac "SSR	pp.19	113	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (0) in H; elpi z_report "pp.19" "114" ltac_term:(G) "H") | idtac "SSR	pp.19	114	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(0) in H; elpi z_report "pp.19" "115" ltac_term:(G) "H") | idtac "SSR	pp.19	115	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(0) in H; elpi z_report "pp.19" "116" ltac_term:(G) "H") | idtac "SSR	pp.19	116	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in 2 + X) in H; elpi z_report "pp.19" "117" ltac_term:(G) "H") | idtac "SSR	pp.19	117	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _) in H; elpi z_report "pp.19" "118" ltac_term:(G) "H") | idtac "SSR	pp.19	118	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X + _) in H; elpi z_report "pp.19" "119" ltac_term:(G) "H") | idtac "SSR	pp.19	119	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(a) in H; elpi z_report "pp.19" "120" ltac_term:(G) "H") | idtac "SSR	pp.19	120	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {2}(a) in H; elpi z_report "pp.19" "121" ltac_term:(G) "H") | idtac "SSR	pp.19	121	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X) in H; elpi z_report "pp.19" "122" ltac_term:(G) "H") | idtac "SSR	pp.19	122	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (X in 2 + a + X) in H; elpi z_report "pp.19" "123" ltac_term:(G) "H") | idtac "SSR	pp.19	123	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := (a) in H; elpi z_report "pp.19" "124" ltac_term:(G) "H") | idtac "SSR	pp.19	124	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {3}(a) in H; elpi z_report "pp.19" "125" ltac_term:(G) "H") | idtac "SSR	pp.19	125	error" ].
let G := type of H in first [ assert_succeeds (set pattern_select_z := {3}(a) in H; elpi z_report "pp.19" "126" ltac_term:(G) "H") | idtac "SSR	pp.19	126	error" ].
Abort.

Goal forall a : nat, (if true then a else 0) = double 2.
intros a.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.20" "1" ltac_term:(G)) | idtac "SSR	pp.20	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((if true then a else 0) = double 2); elpi z_report "pp.20" "2" ltac_term:(G)) | idtac "SSR	pp.20	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.20" "3" ltac_term:(G)) | idtac "SSR	pp.20	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.20" "4" ltac_term:(G)) | idtac "SSR	pp.20	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.20" "5" ltac_term:(G)) | idtac "SSR	pp.20	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.20" "6" ltac_term:(G)) | idtac "SSR	pp.20	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.20" "7" ltac_term:(G)) | idtac "SSR	pp.20	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (true); elpi z_report "pp.20" "8" ltac_term:(G)) | idtac "SSR	pp.20	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(true); elpi z_report "pp.20" "9" ltac_term:(G)) | idtac "SSR	pp.20	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.20" "10" ltac_term:(G)) | idtac "SSR	pp.20	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.20" "11" ltac_term:(G)) | idtac "SSR	pp.20	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.20" "12" ltac_term:(G)) | idtac "SSR	pp.20	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "pp.20" "13" ltac_term:(G)) | idtac "SSR	pp.20	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.20" "14" ltac_term:(G)) | idtac "SSR	pp.20	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.20" "15" ltac_term:(G)) | idtac "SSR	pp.20	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.20" "16" ltac_term:(G)) | idtac "SSR	pp.20	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double _); elpi z_report "pp.20" "17" ltac_term:(G)) | idtac "SSR	pp.20	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.20" "18" ltac_term:(G)) | idtac "SSR	pp.20	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double _ as X in _ = X); elpi z_report "pp.20" "19" ltac_term:(G)) | idtac "SSR	pp.20	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(double 2); elpi z_report "pp.20" "20" ltac_term:(G)) | idtac "SSR	pp.20	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (double); elpi z_report "pp.20" "21" ltac_term:(G)) | idtac "SSR	pp.20	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(double); elpi z_report "pp.20" "22" ltac_term:(G)) | idtac "SSR	pp.20	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "pp.20" "23" ltac_term:(G)) | idtac "SSR	pp.20	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double X); elpi z_report "pp.20" "24" ltac_term:(G)) | idtac "SSR	pp.20	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ = X); elpi z_report "pp.20" "25" ltac_term:(G)) | idtac "SSR	pp.20	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in double X); elpi z_report "pp.20" "26" ltac_term:(G)) | idtac "SSR	pp.20	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = double X); elpi z_report "pp.20" "27" ltac_term:(G)) | idtac "SSR	pp.20	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = double X); elpi z_report "pp.20" "28" ltac_term:(G)) | idtac "SSR	pp.20	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2); elpi z_report "pp.20" "29" ltac_term:(G)) | idtac "SSR	pp.20	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.20" "30" ltac_term:(G)) | idtac "SSR	pp.20	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.20" "31" ltac_term:(G)) | idtac "SSR	pp.20	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "pp.20" "32" ltac_term:(G)) | idtac "SSR	pp.20	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "pp.20" "33" ltac_term:(G)) | idtac "SSR	pp.20	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "pp.20" "34" ltac_term:(G)) | idtac "SSR	pp.20	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ = X); elpi z_report "pp.20" "35" ltac_term:(G)) | idtac "SSR	pp.20	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in double X); elpi z_report "pp.20" "36" ltac_term:(G)) | idtac "SSR	pp.20	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double (S X)); elpi z_report "pp.20" "37" ltac_term:(G)) | idtac "SSR	pp.20	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ = double X); elpi z_report "pp.20" "38" ltac_term:(G)) | idtac "SSR	pp.20	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in double (S X)); elpi z_report "pp.20" "39" ltac_term:(G)) | idtac "SSR	pp.20	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = double (S X)); elpi z_report "pp.20" "40" ltac_term:(G)) | idtac "SSR	pp.20	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = double (S X)); elpi z_report "pp.20" "41" ltac_term:(G)) | idtac "SSR	pp.20	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "pp.20" "42" ltac_term:(G)) | idtac "SSR	pp.20	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "pp.20" "43" ltac_term:(G)) | idtac "SSR	pp.20	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.20" "44" ltac_term:(G)) | idtac "SSR	pp.20	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.20" "45" ltac_term:(G)) | idtac "SSR	pp.20	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "pp.20" "46" ltac_term:(G)) | idtac "SSR	pp.20	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in double (S (S X))); elpi z_report "pp.20" "47" ltac_term:(G)) | idtac "SSR	pp.20	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = double (S (S X))); elpi z_report "pp.20" "48" ltac_term:(G)) | idtac "SSR	pp.20	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.20" "49" ltac_term:(G)) | idtac "SSR	pp.20	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.20" "50" ltac_term:(G)) | idtac "SSR	pp.20	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.20" "51" ltac_term:(G)) | idtac "SSR	pp.20	51	error" ].
Abort.

Goal two_is = two_is.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.21" "1" ltac_term:(G)) | idtac "SSR	pp.21	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(two_is = two_is); elpi z_report "pp.21" "2" ltac_term:(G)) | idtac "SSR	pp.21	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.21" "3" ltac_term:(G)) | idtac "SSR	pp.21	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.21" "4" ltac_term:(G)) | idtac "SSR	pp.21	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2 = _); elpi z_report "pp.21" "5" ltac_term:(G)) | idtac "SSR	pp.21	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 = 1 + 1); elpi z_report "pp.21" "6" ltac_term:(G)) | idtac "SSR	pp.21	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.21" "7" ltac_term:(G)) | idtac "SSR	pp.21	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.21" "8" ltac_term:(G)) | idtac "SSR	pp.21	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.21" "9" ltac_term:(G)) | idtac "SSR	pp.21	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.21" "10" ltac_term:(G)) | idtac "SSR	pp.21	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.21" "11" ltac_term:(G)) | idtac "SSR	pp.21	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "pp.21" "12" ltac_term:(G)) | idtac "SSR	pp.21	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X = _); elpi z_report "pp.21" "13" ltac_term:(G)) | idtac "SSR	pp.21	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = 1 + 1); elpi z_report "pp.21" "14" ltac_term:(G)) | idtac "SSR	pp.21	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2); elpi z_report "pp.21" "15" ltac_term:(G)) | idtac "SSR	pp.21	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.21" "16" ltac_term:(G)) | idtac "SSR	pp.21	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.21" "17" ltac_term:(G)) | idtac "SSR	pp.21	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "pp.21" "18" ltac_term:(G)) | idtac "SSR	pp.21	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "pp.21" "19" ltac_term:(G)) | idtac "SSR	pp.21	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X = _); elpi z_report "pp.21" "20" ltac_term:(G)) | idtac "SSR	pp.21	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X = _); elpi z_report "pp.21" "21" ltac_term:(G)) | idtac "SSR	pp.21	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = 1 + 1); elpi z_report "pp.21" "22" ltac_term:(G)) | idtac "SSR	pp.21	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "pp.21" "23" ltac_term:(G)) | idtac "SSR	pp.21	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "pp.21" "24" ltac_term:(G)) | idtac "SSR	pp.21	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.21" "25" ltac_term:(G)) | idtac "SSR	pp.21	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.21" "26" ltac_term:(G)) | idtac "SSR	pp.21	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "pp.21" "27" ltac_term:(G)) | idtac "SSR	pp.21	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) = _); elpi z_report "pp.21" "28" ltac_term:(G)) | idtac "SSR	pp.21	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.21" "29" ltac_term:(G)) | idtac "SSR	pp.21	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.21" "30" ltac_term:(G)) | idtac "SSR	pp.21	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "pp.21" "31" ltac_term:(G)) | idtac "SSR	pp.21	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 2 = X); elpi z_report "pp.21" "32" ltac_term:(G)) | idtac "SSR	pp.21	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "pp.21" "33" ltac_term:(G)) | idtac "SSR	pp.21	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + 1); elpi z_report "pp.21" "34" ltac_term:(G)) | idtac "SSR	pp.21	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.21" "35" ltac_term:(G)) | idtac "SSR	pp.21	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.21" "36" ltac_term:(G)) | idtac "SSR	pp.21	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "pp.21" "37" ltac_term:(G)) | idtac "SSR	pp.21	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _); elpi z_report "pp.21" "38" ltac_term:(G)) | idtac "SSR	pp.21	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "pp.21" "39" ltac_term:(G)) | idtac "SSR	pp.21	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = X + _); elpi z_report "pp.21" "40" ltac_term:(G)) | idtac "SSR	pp.21	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "pp.21" "41" ltac_term:(G)) | idtac "SSR	pp.21	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "pp.21" "42" ltac_term:(G)) | idtac "SSR	pp.21	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in 2 = X); elpi z_report "pp.21" "43" ltac_term:(G)) | idtac "SSR	pp.21	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "pp.21" "44" ltac_term:(G)) | idtac "SSR	pp.21	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "pp.21" "45" ltac_term:(G)) | idtac "SSR	pp.21	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _); elpi z_report "pp.21" "46" ltac_term:(G)) | idtac "SSR	pp.21	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = S X + _); elpi z_report "pp.21" "47" ltac_term:(G)) | idtac "SSR	pp.21	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.21" "48" ltac_term:(G)) | idtac "SSR	pp.21	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.21" "49" ltac_term:(G)) | idtac "SSR	pp.21	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "pp.21" "50" ltac_term:(G)) | idtac "SSR	pp.21	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X); elpi z_report "pp.21" "51" ltac_term:(G)) | idtac "SSR	pp.21	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "pp.21" "52" ltac_term:(G)) | idtac "SSR	pp.21	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ = _ + X); elpi z_report "pp.21" "53" ltac_term:(G)) | idtac "SSR	pp.21	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "pp.21" "54" ltac_term:(G)) | idtac "SSR	pp.21	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in 2 = X); elpi z_report "pp.21" "55" ltac_term:(G)) | idtac "SSR	pp.21	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "pp.21" "56" ltac_term:(G)) | idtac "SSR	pp.21	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "pp.21" "57" ltac_term:(G)) | idtac "SSR	pp.21	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in 2 = X); elpi z_report "pp.21" "58" ltac_term:(G)) | idtac "SSR	pp.21	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "pp.21" "59" ltac_term:(G)) | idtac "SSR	pp.21	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(S); elpi z_report "pp.21" "60" ltac_term:(G)) | idtac "SSR	pp.21	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(S); elpi z_report "pp.21" "61" ltac_term:(G)) | idtac "SSR	pp.21	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X); elpi z_report "pp.21" "62" ltac_term:(G)) | idtac "SSR	pp.21	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + S X); elpi z_report "pp.21" "63" ltac_term:(G)) | idtac "SSR	pp.21	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.21" "64" ltac_term:(G)) | idtac "SSR	pp.21	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "pp.21" "65" ltac_term:(G)) | idtac "SSR	pp.21	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "pp.21" "66" ltac_term:(G)) | idtac "SSR	pp.21	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.21" "67" ltac_term:(G)) | idtac "SSR	pp.21	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(two_is); elpi z_report "pp.21" "68" ltac_term:(G)) | idtac "SSR	pp.21	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(two_is); elpi z_report "pp.21" "69" ltac_term:(G)) | idtac "SSR	pp.21	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.21" "70" ltac_term:(G)) | idtac "SSR	pp.21	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (two_is); elpi z_report "pp.21" "71" ltac_term:(G)) | idtac "SSR	pp.21	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(two_is); elpi z_report "pp.21" "72" ltac_term:(G)) | idtac "SSR	pp.21	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(two_is); elpi z_report "pp.21" "73" ltac_term:(G)) | idtac "SSR	pp.21	73	error" ].
Abort.

Goal forall a b : nat, a + b * 2 = b /\ forall n : nat, n * n = 0.
intros a b.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "pp.22" "1" ltac_term:(G)) | idtac "SSR	pp.22	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b * 2 = b /\ (forall n : nat, n * n = 0)); elpi z_report "pp.22" "2" ltac_term:(G)) | idtac "SSR	pp.22	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "pp.22" "3" ltac_term:(G)) | idtac "SSR	pp.22	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "pp.22" "4" ltac_term:(G)) | idtac "SSR	pp.22	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "pp.22" "5" ltac_term:(G)) | idtac "SSR	pp.22	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "pp.22" "6" ltac_term:(G)) | idtac "SSR	pp.22	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _ as X in X /\ _); elpi z_report "pp.22" "7" ltac_term:(G)) | idtac "SSR	pp.22	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b * 2 = b); elpi z_report "pp.22" "8" ltac_term:(G)) | idtac "SSR	pp.22	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.22" "9" ltac_term:(G)) | idtac "SSR	pp.22	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.22" "10" ltac_term:(G)) | idtac "SSR	pp.22	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.22" "11" ltac_term:(G)) | idtac "SSR	pp.22	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.22" "12" ltac_term:(G)) | idtac "SSR	pp.22	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "pp.22" "13" ltac_term:(G)) | idtac "SSR	pp.22	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "pp.22" "14" ltac_term:(G)) | idtac "SSR	pp.22	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "pp.22" "15" ltac_term:(G)) | idtac "SSR	pp.22	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X /\ _); elpi z_report "pp.22" "16" ltac_term:(G)) | idtac "SSR	pp.22	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _ /\ _); elpi z_report "pp.22" "17" ltac_term:(G)) | idtac "SSR	pp.22	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _ /\ _); elpi z_report "pp.22" "18" ltac_term:(G)) | idtac "SSR	pp.22	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b * 2); elpi z_report "pp.22" "19" ltac_term:(G)) | idtac "SSR	pp.22	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "pp.22" "20" ltac_term:(G)) | idtac "SSR	pp.22	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "pp.22" "21" ltac_term:(G)) | idtac "SSR	pp.22	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "pp.22" "22" ltac_term:(G)) | idtac "SSR	pp.22	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "pp.22" "23" ltac_term:(G)) | idtac "SSR	pp.22	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "pp.22" "24" ltac_term:(G)) | idtac "SSR	pp.22	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _ /\ _); elpi z_report "pp.22" "25" ltac_term:(G)) | idtac "SSR	pp.22	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "pp.22" "26" ltac_term:(G)) | idtac "SSR	pp.22	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "pp.22" "27" ltac_term:(G)) | idtac "SSR	pp.22	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "pp.22" "28" ltac_term:(G)) | idtac "SSR	pp.22	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X); elpi z_report "pp.22" "29" ltac_term:(G)) | idtac "SSR	pp.22	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _); elpi z_report "pp.22" "30" ltac_term:(G)) | idtac "SSR	pp.22	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X /\ _); elpi z_report "pp.22" "31" ltac_term:(G)) | idtac "SSR	pp.22	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "pp.22" "32" ltac_term:(G)) | idtac "SSR	pp.22	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X = _); elpi z_report "pp.22" "33" ltac_term:(G)) | idtac "SSR	pp.22	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _ /\ _); elpi z_report "pp.22" "34" ltac_term:(G)) | idtac "SSR	pp.22	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _ /\ _); elpi z_report "pp.22" "35" ltac_term:(G)) | idtac "SSR	pp.22	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X = _ /\ _); elpi z_report "pp.22" "36" ltac_term:(G)) | idtac "SSR	pp.22	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b * 2); elpi z_report "pp.22" "37" ltac_term:(G)) | idtac "SSR	pp.22	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.mul); elpi z_report "pp.22" "38" ltac_term:(G)) | idtac "SSR	pp.22	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.mul); elpi z_report "pp.22" "39" ltac_term:(G)) | idtac "SSR	pp.22	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "pp.22" "40" ltac_term:(G)) | idtac "SSR	pp.22	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _); elpi z_report "pp.22" "41" ltac_term:(G)) | idtac "SSR	pp.22	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _ = _); elpi z_report "pp.22" "42" ltac_term:(G)) | idtac "SSR	pp.22	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _ = _ /\ _); elpi z_report "pp.22" "43" ltac_term:(G)) | idtac "SSR	pp.22	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.22" "44" ltac_term:(G)) | idtac "SSR	pp.22	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "pp.22" "45" ltac_term:(G)) | idtac "SSR	pp.22	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "pp.22" "46" ltac_term:(G)) | idtac "SSR	pp.22	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "pp.22" "47" ltac_term:(G)) | idtac "SSR	pp.22	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ * X); elpi z_report "pp.22" "48" ltac_term:(G)) | idtac "SSR	pp.22	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "pp.22" "49" ltac_term:(G)) | idtac "SSR	pp.22	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X); elpi z_report "pp.22" "50" ltac_term:(G)) | idtac "SSR	pp.22	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X /\ _); elpi z_report "pp.22" "51" ltac_term:(G)) | idtac "SSR	pp.22	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X); elpi z_report "pp.22" "52" ltac_term:(G)) | idtac "SSR	pp.22	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + _ * X); elpi z_report "pp.22" "53" ltac_term:(G)) | idtac "SSR	pp.22	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X = _); elpi z_report "pp.22" "54" ltac_term:(G)) | idtac "SSR	pp.22	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _ /\ _); elpi z_report "pp.22" "55" ltac_term:(G)) | idtac "SSR	pp.22	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X = _); elpi z_report "pp.22" "56" ltac_term:(G)) | idtac "SSR	pp.22	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + _ * X = _); elpi z_report "pp.22" "57" ltac_term:(G)) | idtac "SSR	pp.22	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X = _ /\ _); elpi z_report "pp.22" "58" ltac_term:(G)) | idtac "SSR	pp.22	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + _ * X = _ /\ _); elpi z_report "pp.22" "59" ltac_term:(G)) | idtac "SSR	pp.22	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2); elpi z_report "pp.22" "60" ltac_term:(G)) | idtac "SSR	pp.22	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.22" "61" ltac_term:(G)) | idtac "SSR	pp.22	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "pp.22" "62" ltac_term:(G)) | idtac "SSR	pp.22	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "pp.22" "63" ltac_term:(G)) | idtac "SSR	pp.22	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "pp.22" "64" ltac_term:(G)) | idtac "SSR	pp.22	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "pp.22" "65" ltac_term:(G)) | idtac "SSR	pp.22	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = _); elpi z_report "pp.22" "66" ltac_term:(G)) | idtac "SSR	pp.22	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X); elpi z_report "pp.22" "67" ltac_term:(G)) | idtac "SSR	pp.22	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ * X); elpi z_report "pp.22" "68" ltac_term:(G)) | idtac "SSR	pp.22	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * S X); elpi z_report "pp.22" "69" ltac_term:(G)) | idtac "SSR	pp.22	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ * S X); elpi z_report "pp.22" "70" ltac_term:(G)) | idtac "SSR	pp.22	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X = _); elpi z_report "pp.22" "71" ltac_term:(G)) | idtac "SSR	pp.22	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + _ * X); elpi z_report "pp.22" "72" ltac_term:(G)) | idtac "SSR	pp.22	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = _ /\ _); elpi z_report "pp.22" "73" ltac_term:(G)) | idtac "SSR	pp.22	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * S X); elpi z_report "pp.22" "74" ltac_term:(G)) | idtac "SSR	pp.22	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + _ * S X); elpi z_report "pp.22" "75" ltac_term:(G)) | idtac "SSR	pp.22	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * S X = _); elpi z_report "pp.22" "76" ltac_term:(G)) | idtac "SSR	pp.22	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + _ * S X = _); elpi z_report "pp.22" "77" ltac_term:(G)) | idtac "SSR	pp.22	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * S X = _ /\ _); elpi z_report "pp.22" "78" ltac_term:(G)) | idtac "SSR	pp.22	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + _ * S X = _ /\ _); elpi z_report "pp.22" "79" ltac_term:(G)) | idtac "SSR	pp.22	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "pp.22" "80" ltac_term:(G)) | idtac "SSR	pp.22	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "pp.22" "81" ltac_term:(G)) | idtac "SSR	pp.22	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.22" "82" ltac_term:(G)) | idtac "SSR	pp.22	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "pp.22" "83" ltac_term:(G)) | idtac "SSR	pp.22	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "pp.22" "84" ltac_term:(G)) | idtac "SSR	pp.22	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * S (S X)); elpi z_report "pp.22" "85" ltac_term:(G)) | idtac "SSR	pp.22	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * S (S X)); elpi z_report "pp.22" "86" ltac_term:(G)) | idtac "SSR	pp.22	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * S (S X) = _); elpi z_report "pp.22" "87" ltac_term:(G)) | idtac "SSR	pp.22	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * S (S X) = _ /\ _); elpi z_report "pp.22" "88" ltac_term:(G)) | idtac "SSR	pp.22	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.22" "89" ltac_term:(G)) | idtac "SSR	pp.22	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.22" "90" ltac_term:(G)) | idtac "SSR	pp.22	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "pp.22" "91" ltac_term:(G)) | idtac "SSR	pp.22	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X /\ _); elpi z_report "pp.22" "92" ltac_term:(G)) | idtac "SSR	pp.22	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "pp.22" "93" ltac_term:(G)) | idtac "SSR	pp.22	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.22" "94" ltac_term:(G)) | idtac "SSR	pp.22	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "pp.22" "95" ltac_term:(G)) | idtac "SSR	pp.22	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "pp.22" "96" ltac_term:(G)) | idtac "SSR	pp.22	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (forall n : nat, n * n = 0); elpi z_report "pp.22" "97" ltac_term:(G)) | idtac "SSR	pp.22	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(forall n : nat, n * n = 0); elpi z_report "pp.22" "98" ltac_term:(G)) | idtac "SSR	pp.22	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.22" "99" ltac_term:(G)) | idtac "SSR	pp.22	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.22" "100" ltac_term:(G)) | idtac "SSR	pp.22	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.22" "101" ltac_term:(G)) | idtac "SSR	pp.22	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.22" "102" ltac_term:(G)) | idtac "SSR	pp.22	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(@eq); elpi z_report "pp.22" "103" ltac_term:(G)) | idtac "SSR	pp.22	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.22" "104" ltac_term:(G)) | idtac "SSR	pp.22	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.22" "105" ltac_term:(G)) | idtac "SSR	pp.22	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.22" "106" ltac_term:(G)) | idtac "SSR	pp.22	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.mul); elpi z_report "pp.22" "107" ltac_term:(G)) | idtac "SSR	pp.22	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.mul); elpi z_report "pp.22" "108" ltac_term:(G)) | idtac "SSR	pp.22	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.mul); elpi z_report "pp.22" "109" ltac_term:(G)) | idtac "SSR	pp.22	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.22" "110" ltac_term:(G)) | idtac "SSR	pp.22	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.22" "111" ltac_term:(G)) | idtac "SSR	pp.22	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "pp.22" "112" ltac_term:(G)) | idtac "SSR	pp.22	112	error" ].
Abort.

Goal (exists m : nat, m = 0) /\ True.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ /\ _); elpi z_report "pp.23" "1" ltac_term:(G)) | idtac "SSR	pp.23	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((exists m : nat, m = 0) /\ True); elpi z_report "pp.23" "2" ltac_term:(G)) | idtac "SSR	pp.23	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (and); elpi z_report "pp.23" "3" ltac_term:(G)) | idtac "SSR	pp.23	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(and); elpi z_report "pp.23" "4" ltac_term:(G)) | idtac "SSR	pp.23	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X /\ _); elpi z_report "pp.23" "5" ltac_term:(G)) | idtac "SSR	pp.23	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(exists m : nat, m = 0); elpi z_report "pp.23" "6" ltac_term:(G)) | idtac "SSR	pp.23	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (ex); elpi z_report "pp.23" "7" ltac_term:(G)) | idtac "SSR	pp.23	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(ex); elpi z_report "pp.23" "8" ltac_term:(G)) | idtac "SSR	pp.23	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.23" "9" ltac_term:(G)) | idtac "SSR	pp.23	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "pp.23" "10" ltac_term:(G)) | idtac "SSR	pp.23	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.23" "11" ltac_term:(G)) | idtac "SSR	pp.23	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "pp.23" "12" ltac_term:(G)) | idtac "SSR	pp.23	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "pp.23" "13" ltac_term:(G)) | idtac "SSR	pp.23	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "pp.23" "14" ltac_term:(G)) | idtac "SSR	pp.23	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "pp.23" "15" ltac_term:(G)) | idtac "SSR	pp.23	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.23" "16" ltac_term:(G)) | idtac "SSR	pp.23	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(nat); elpi z_report "pp.23" "17" ltac_term:(G)) | idtac "SSR	pp.23	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "pp.23" "18" ltac_term:(G)) | idtac "SSR	pp.23	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "pp.23" "19" ltac_term:(G)) | idtac "SSR	pp.23	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (True); elpi z_report "pp.23" "20" ltac_term:(G)) | idtac "SSR	pp.23	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ /\ X); elpi z_report "pp.23" "21" ltac_term:(G)) | idtac "SSR	pp.23	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(True); elpi z_report "pp.23" "22" ltac_term:(G)) | idtac "SSR	pp.23	22	error" ].
Abort.
