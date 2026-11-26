(* Differential corpus: the examples of the paper (Gonthier and Tassi, ITP
   2012), 1 to 10, with the paper's patterns and every pattern that
   select_all and point_to_pattern produce.  Run by run.sh. *)
From elpi Require Import elpi.
From coq_tmp.select.tests Require Import diff_support.
From Stdlib Require Import List.

Module Paper.
Section Ring.
Variables (R : Type) (zero two : R) (add mul : R -> R -> R) (opp : R -> R).
Variables (f : R -> R) (f2 : R -> R -> R).
Declare Scope ring_scope.
Delimit Scope ring_scope with ring.
Local Notation "0" := zero : ring_scope.
Local Notation "2" := two : ring_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "x - y" := (add x (opp y)) : ring_scope.
Local Open Scope ring_scope.

Goal forall a b c : R, a + (b * c - a) + a = b * c + a.
intros a b c.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - a); elpi z_report "paper.ex1" "1" ltac_term:(G)) | idtac "SSR	paper.ex1	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * c + _); elpi z_report "paper.ex1" "2" ltac_term:(G)) | idtac "SSR	paper.ex1	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex1" "3" ltac_term:(G)) | idtac "SSR	paper.ex1	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex1g" "1" ltac_term:(G)) | idtac "SSR	paper.ex1g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + (b * c - a) + a = b * c + a); elpi z_report "paper.ex1g" "2" ltac_term:(G)) | idtac "SSR	paper.ex1g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex1g" "3" ltac_term:(G)) | idtac "SSR	paper.ex1g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex1g" "4" ltac_term:(G)) | idtac "SSR	paper.ex1g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (R); elpi z_report "paper.ex1g" "5" ltac_term:(G)) | idtac "SSR	paper.ex1g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex1g" "6" ltac_term:(G)) | idtac "SSR	paper.ex1g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex1g" "7" ltac_term:(G)) | idtac "SSR	paper.ex1g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex1g" "8" ltac_term:(G)) | idtac "SSR	paper.ex1g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.ex1g" "9" ltac_term:(G)) | idtac "SSR	paper.ex1g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + (b * c - a) + a); elpi z_report "paper.ex1g" "10" ltac_term:(G)) | idtac "SSR	paper.ex1g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex1g" "11" ltac_term:(G)) | idtac "SSR	paper.ex1g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex1g" "12" ltac_term:(G)) | idtac "SSR	paper.ex1g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex1g" "13" ltac_term:(G)) | idtac "SSR	paper.ex1g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "paper.ex1g" "14" ltac_term:(G)) | idtac "SSR	paper.ex1g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "paper.ex1g" "15" ltac_term:(G)) | idtac "SSR	paper.ex1g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.ex1g" "16" ltac_term:(G)) | idtac "SSR	paper.ex1g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X = _); elpi z_report "paper.ex1g" "17" ltac_term:(G)) | idtac "SSR	paper.ex1g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "paper.ex1g" "18" ltac_term:(G)) | idtac "SSR	paper.ex1g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + (b * c - a)); elpi z_report "paper.ex1g" "19" ltac_term:(G)) | idtac "SSR	paper.ex1g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex1g" "20" ltac_term:(G)) | idtac "SSR	paper.ex1g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex1g" "21" ltac_term:(G)) | idtac "SSR	paper.ex1g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "paper.ex1g" "22" ltac_term:(G)) | idtac "SSR	paper.ex1g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "paper.ex1g" "23" ltac_term:(G)) | idtac "SSR	paper.ex1g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (b * c - a)); elpi z_report "paper.ex1g" "24" ltac_term:(G)) | idtac "SSR	paper.ex1g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex1g" "25" ltac_term:(G)) | idtac "SSR	paper.ex1g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex1g" "26" ltac_term:(G)) | idtac "SSR	paper.ex1g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - a); elpi z_report "paper.ex1g" "27" ltac_term:(G)) | idtac "SSR	paper.ex1g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + X); elpi z_report "paper.ex1g" "28" ltac_term:(G)) | idtac "SSR	paper.ex1g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "paper.ex1g" "29" ltac_term:(G)) | idtac "SSR	paper.ex1g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "paper.ex1g" "30" ltac_term:(G)) | idtac "SSR	paper.ex1g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - a in X in X = _); elpi z_report "paper.ex1g" "31" ltac_term:(G)) | idtac "SSR	paper.ex1g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - a in X in X + _); elpi z_report "paper.ex1g" "32" ltac_term:(G)) | idtac "SSR	paper.ex1g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _); elpi z_report "paper.ex1g" "33" ltac_term:(G)) | idtac "SSR	paper.ex1g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "paper.ex1g" "34" ltac_term:(G)) | idtac "SSR	paper.ex1g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - a in X in X + _ = _); elpi z_report "paper.ex1g" "35" ltac_term:(G)) | idtac "SSR	paper.ex1g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _ = _); elpi z_report "paper.ex1g" "36" ltac_term:(G)) | idtac "SSR	paper.ex1g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b * c - a); elpi z_report "paper.ex1g" "37" ltac_term:(G)) | idtac "SSR	paper.ex1g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex1g" "38" ltac_term:(G)) | idtac "SSR	paper.ex1g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex1g" "39" ltac_term:(G)) | idtac "SSR	paper.ex1g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X - a); elpi z_report "paper.ex1g" "40" ltac_term:(G)) | idtac "SSR	paper.ex1g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in X + _); elpi z_report "paper.ex1g" "41" ltac_term:(G)) | idtac "SSR	paper.ex1g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _); elpi z_report "paper.ex1g" "42" ltac_term:(G)) | idtac "SSR	paper.ex1g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + _); elpi z_report "paper.ex1g" "43" ltac_term:(G)) | idtac "SSR	paper.ex1g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "paper.ex1g" "44" ltac_term:(G)) | idtac "SSR	paper.ex1g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in a + X); elpi z_report "paper.ex1g" "45" ltac_term:(G)) | idtac "SSR	paper.ex1g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + _ = _); elpi z_report "paper.ex1g" "46" ltac_term:(G)) | idtac "SSR	paper.ex1g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ + X + _); elpi z_report "paper.ex1g" "47" ltac_term:(G)) | idtac "SSR	paper.ex1g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + (X + _)); elpi z_report "paper.ex1g" "48" ltac_term:(G)) | idtac "SSR	paper.ex1g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _); elpi z_report "paper.ex1g" "49" ltac_term:(G)) | idtac "SSR	paper.ex1g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + (X + _) + _); elpi z_report "paper.ex1g" "50" ltac_term:(G)) | idtac "SSR	paper.ex1g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _ = _); elpi z_report "paper.ex1g" "51" ltac_term:(G)) | idtac "SSR	paper.ex1g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + (X + _) + _ = _); elpi z_report "paper.ex1g" "52" ltac_term:(G)) | idtac "SSR	paper.ex1g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ * _); elpi z_report "paper.ex1g" "53" ltac_term:(G)) | idtac "SSR	paper.ex1g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b * c); elpi z_report "paper.ex1g" "54" ltac_term:(G)) | idtac "SSR	paper.ex1g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex1g" "55" ltac_term:(G)) | idtac "SSR	paper.ex1g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex1g" "56" ltac_term:(G)) | idtac "SSR	paper.ex1g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _ + _); elpi z_report "paper.ex1g" "57" ltac_term:(G)) | idtac "SSR	paper.ex1g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X * _ + _)); elpi z_report "paper.ex1g" "58" ltac_term:(G)) | idtac "SSR	paper.ex1g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X * _ + _) + _); elpi z_report "paper.ex1g" "59" ltac_term:(G)) | idtac "SSR	paper.ex1g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X * _ + _) + _ = _); elpi z_report "paper.ex1g" "60" ltac_term:(G)) | idtac "SSR	paper.ex1g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex1g" "61" ltac_term:(G)) | idtac "SSR	paper.ex1g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex1g" "62" ltac_term:(G)) | idtac "SSR	paper.ex1g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X * _); elpi z_report "paper.ex1g" "63" ltac_term:(G)) | idtac "SSR	paper.ex1g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X + _); elpi z_report "paper.ex1g" "64" ltac_term:(G)) | idtac "SSR	paper.ex1g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ * X + _)); elpi z_report "paper.ex1g" "65" ltac_term:(G)) | idtac "SSR	paper.ex1g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ * X + _) + _); elpi z_report "paper.ex1g" "66" ltac_term:(G)) | idtac "SSR	paper.ex1g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ * X + _) + _ = _); elpi z_report "paper.ex1g" "67" ltac_term:(G)) | idtac "SSR	paper.ex1g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex1g" "68" ltac_term:(G)) | idtac "SSR	paper.ex1g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex1g" "69" ltac_term:(G)) | idtac "SSR	paper.ex1g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ * X); elpi z_report "paper.ex1g" "70" ltac_term:(G)) | idtac "SSR	paper.ex1g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _); elpi z_report "paper.ex1g" "71" ltac_term:(G)) | idtac "SSR	paper.ex1g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + X); elpi z_report "paper.ex1g" "72" ltac_term:(G)) | idtac "SSR	paper.ex1g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in X = _); elpi z_report "paper.ex1g" "73" ltac_term:(G)) | idtac "SSR	paper.ex1g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in X + _); elpi z_report "paper.ex1g" "74" ltac_term:(G)) | idtac "SSR	paper.ex1g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "paper.ex1g" "75" ltac_term:(G)) | idtac "SSR	paper.ex1g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in a + X); elpi z_report "paper.ex1g" "76" ltac_term:(G)) | idtac "SSR	paper.ex1g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in X + _ = _); elpi z_report "paper.ex1g" "77" ltac_term:(G)) | idtac "SSR	paper.ex1g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in _ + X + _); elpi z_report "paper.ex1g" "78" ltac_term:(G)) | idtac "SSR	paper.ex1g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + (_ + X)); elpi z_report "paper.ex1g" "79" ltac_term:(G)) | idtac "SSR	paper.ex1g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _); elpi z_report "paper.ex1g" "80" ltac_term:(G)) | idtac "SSR	paper.ex1g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b * c + X); elpi z_report "paper.ex1g" "81" ltac_term:(G)) | idtac "SSR	paper.ex1g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + (_ + X) + _); elpi z_report "paper.ex1g" "82" ltac_term:(G)) | idtac "SSR	paper.ex1g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _ = _); elpi z_report "paper.ex1g" "83" ltac_term:(G)) | idtac "SSR	paper.ex1g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + (_ + X) + _ = _); elpi z_report "paper.ex1g" "84" ltac_term:(G)) | idtac "SSR	paper.ex1g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(- a); elpi z_report "paper.ex1g" "85" ltac_term:(G)) | idtac "SSR	paper.ex1g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (opp); elpi z_report "paper.ex1g" "86" ltac_term:(G)) | idtac "SSR	paper.ex1g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(opp); elpi z_report "paper.ex1g" "87" ltac_term:(G)) | idtac "SSR	paper.ex1g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in - X); elpi z_report "paper.ex1g" "88" ltac_term:(G)) | idtac "SSR	paper.ex1g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ - X); elpi z_report "paper.ex1g" "89" ltac_term:(G)) | idtac "SSR	paper.ex1g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ - X)); elpi z_report "paper.ex1g" "90" ltac_term:(G)) | idtac "SSR	paper.ex1g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ - X) + _); elpi z_report "paper.ex1g" "91" ltac_term:(G)) | idtac "SSR	paper.ex1g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ - X) + _ = _); elpi z_report "paper.ex1g" "92" ltac_term:(G)) | idtac "SSR	paper.ex1g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex1g" "93" ltac_term:(G)) | idtac "SSR	paper.ex1g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex1g" "94" ltac_term:(G)) | idtac "SSR	paper.ex1g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex1g" "95" ltac_term:(G)) | idtac "SSR	paper.ex1g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.ex1g" "96" ltac_term:(G)) | idtac "SSR	paper.ex1g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex1g" "97" ltac_term:(G)) | idtac "SSR	paper.ex1g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex1g" "98" ltac_term:(G)) | idtac "SSR	paper.ex1g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex1g" "99" ltac_term:(G)) | idtac "SSR	paper.ex1g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "paper.ex1g" "100" ltac_term:(G)) | idtac "SSR	paper.ex1g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * c + a); elpi z_report "paper.ex1g" "101" ltac_term:(G)) | idtac "SSR	paper.ex1g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b * c + a); elpi z_report "paper.ex1g" "102" ltac_term:(G)) | idtac "SSR	paper.ex1g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (add); elpi z_report "paper.ex1g" "103" ltac_term:(G)) | idtac "SSR	paper.ex1g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex1g" "104" ltac_term:(G)) | idtac "SSR	paper.ex1g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex1g" "105" ltac_term:(G)) | idtac "SSR	paper.ex1g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ = X); elpi z_report "paper.ex1g" "106" ltac_term:(G)) | idtac "SSR	paper.ex1g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "paper.ex1g" "107" ltac_term:(G)) | idtac "SSR	paper.ex1g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in X + a); elpi z_report "paper.ex1g" "108" ltac_term:(G)) | idtac "SSR	paper.ex1g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ = X + _); elpi z_report "paper.ex1g" "109" ltac_term:(G)) | idtac "SSR	paper.ex1g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "paper.ex1g" "110" ltac_term:(G)) | idtac "SSR	paper.ex1g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ * _); elpi z_report "paper.ex1g" "111" ltac_term:(G)) | idtac "SSR	paper.ex1g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b * c); elpi z_report "paper.ex1g" "112" ltac_term:(G)) | idtac "SSR	paper.ex1g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mul); elpi z_report "paper.ex1g" "113" ltac_term:(G)) | idtac "SSR	paper.ex1g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex1g" "114" ltac_term:(G)) | idtac "SSR	paper.ex1g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex1g" "115" ltac_term:(G)) | idtac "SSR	paper.ex1g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _ + a); elpi z_report "paper.ex1g" "116" ltac_term:(G)) | idtac "SSR	paper.ex1g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X * _ + _); elpi z_report "paper.ex1g" "117" ltac_term:(G)) | idtac "SSR	paper.ex1g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "paper.ex1g" "118" ltac_term:(G)) | idtac "SSR	paper.ex1g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "paper.ex1g" "119" ltac_term:(G)) | idtac "SSR	paper.ex1g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex1g" "120" ltac_term:(G)) | idtac "SSR	paper.ex1g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex1g" "121" ltac_term:(G)) | idtac "SSR	paper.ex1g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X * _); elpi z_report "paper.ex1g" "122" ltac_term:(G)) | idtac "SSR	paper.ex1g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X + a); elpi z_report "paper.ex1g" "123" ltac_term:(G)) | idtac "SSR	paper.ex1g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ * X + _); elpi z_report "paper.ex1g" "124" ltac_term:(G)) | idtac "SSR	paper.ex1g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "paper.ex1g" "125" ltac_term:(G)) | idtac "SSR	paper.ex1g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "paper.ex1g" "126" ltac_term:(G)) | idtac "SSR	paper.ex1g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "paper.ex1g" "127" ltac_term:(G)) | idtac "SSR	paper.ex1g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "paper.ex1g" "128" ltac_term:(G)) | idtac "SSR	paper.ex1g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ * X); elpi z_report "paper.ex1g" "129" ltac_term:(G)) | idtac "SSR	paper.ex1g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "paper.ex1g" "130" ltac_term:(G)) | idtac "SSR	paper.ex1g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "paper.ex1g" "131" ltac_term:(G)) | idtac "SSR	paper.ex1g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "paper.ex1g" "132" ltac_term:(G)) | idtac "SSR	paper.ex1g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "paper.ex1g" "133" ltac_term:(G)) | idtac "SSR	paper.ex1g	133	error" ].
Abort.

Goal forall a b c : R, a + (b * c + a) + a = b * c + a.
intros a b c.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - a); elpi z_report "paper.ex2" "1" ltac_term:(G)) | idtac "SSR	paper.ex2	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * c + _); elpi z_report "paper.ex2" "2" ltac_term:(G)) | idtac "SSR	paper.ex2	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex2g" "1" ltac_term:(G)) | idtac "SSR	paper.ex2g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + (b * c + a) + a = b * c + a); elpi z_report "paper.ex2g" "2" ltac_term:(G)) | idtac "SSR	paper.ex2g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex2g" "3" ltac_term:(G)) | idtac "SSR	paper.ex2g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex2g" "4" ltac_term:(G)) | idtac "SSR	paper.ex2g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (R); elpi z_report "paper.ex2g" "5" ltac_term:(G)) | idtac "SSR	paper.ex2g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex2g" "6" ltac_term:(G)) | idtac "SSR	paper.ex2g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex2g" "7" ltac_term:(G)) | idtac "SSR	paper.ex2g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex2g" "8" ltac_term:(G)) | idtac "SSR	paper.ex2g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.ex2g" "9" ltac_term:(G)) | idtac "SSR	paper.ex2g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + (b * c + a) + a); elpi z_report "paper.ex2g" "10" ltac_term:(G)) | idtac "SSR	paper.ex2g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex2g" "11" ltac_term:(G)) | idtac "SSR	paper.ex2g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex2g" "12" ltac_term:(G)) | idtac "SSR	paper.ex2g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex2g" "13" ltac_term:(G)) | idtac "SSR	paper.ex2g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "paper.ex2g" "14" ltac_term:(G)) | idtac "SSR	paper.ex2g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "paper.ex2g" "15" ltac_term:(G)) | idtac "SSR	paper.ex2g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.ex2g" "16" ltac_term:(G)) | idtac "SSR	paper.ex2g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X = _); elpi z_report "paper.ex2g" "17" ltac_term:(G)) | idtac "SSR	paper.ex2g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "paper.ex2g" "18" ltac_term:(G)) | idtac "SSR	paper.ex2g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + (b * c + a)); elpi z_report "paper.ex2g" "19" ltac_term:(G)) | idtac "SSR	paper.ex2g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex2g" "20" ltac_term:(G)) | idtac "SSR	paper.ex2g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex2g" "21" ltac_term:(G)) | idtac "SSR	paper.ex2g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "paper.ex2g" "22" ltac_term:(G)) | idtac "SSR	paper.ex2g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "paper.ex2g" "23" ltac_term:(G)) | idtac "SSR	paper.ex2g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (b * c + a)); elpi z_report "paper.ex2g" "24" ltac_term:(G)) | idtac "SSR	paper.ex2g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex2g" "25" ltac_term:(G)) | idtac "SSR	paper.ex2g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex2g" "26" ltac_term:(G)) | idtac "SSR	paper.ex2g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + X); elpi z_report "paper.ex2g" "27" ltac_term:(G)) | idtac "SSR	paper.ex2g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "paper.ex2g" "28" ltac_term:(G)) | idtac "SSR	paper.ex2g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "paper.ex2g" "29" ltac_term:(G)) | idtac "SSR	paper.ex2g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + a in X in X + _); elpi z_report "paper.ex2g" "30" ltac_term:(G)) | idtac "SSR	paper.ex2g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _); elpi z_report "paper.ex2g" "31" ltac_term:(G)) | idtac "SSR	paper.ex2g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "paper.ex2g" "32" ltac_term:(G)) | idtac "SSR	paper.ex2g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + a in X in X + _ = _); elpi z_report "paper.ex2g" "33" ltac_term:(G)) | idtac "SSR	paper.ex2g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _ = _); elpi z_report "paper.ex2g" "34" ltac_term:(G)) | idtac "SSR	paper.ex2g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * c + _ in X in X = _); elpi z_report "paper.ex2g" "35" ltac_term:(G)) | idtac "SSR	paper.ex2g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b * c + _); elpi z_report "paper.ex2g" "36" ltac_term:(G)) | idtac "SSR	paper.ex2g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b * c + a); elpi z_report "paper.ex2g" "37" ltac_term:(G)) | idtac "SSR	paper.ex2g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex2g" "38" ltac_term:(G)) | idtac "SSR	paper.ex2g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex2g" "39" ltac_term:(G)) | idtac "SSR	paper.ex2g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _); elpi z_report "paper.ex2g" "40" ltac_term:(G)) | idtac "SSR	paper.ex2g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + _); elpi z_report "paper.ex2g" "41" ltac_term:(G)) | idtac "SSR	paper.ex2g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "paper.ex2g" "42" ltac_term:(G)) | idtac "SSR	paper.ex2g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in a + X); elpi z_report "paper.ex2g" "43" ltac_term:(G)) | idtac "SSR	paper.ex2g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + _ = _); elpi z_report "paper.ex2g" "44" ltac_term:(G)) | idtac "SSR	paper.ex2g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ + X + _); elpi z_report "paper.ex2g" "45" ltac_term:(G)) | idtac "SSR	paper.ex2g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + (X + _)); elpi z_report "paper.ex2g" "46" ltac_term:(G)) | idtac "SSR	paper.ex2g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _); elpi z_report "paper.ex2g" "47" ltac_term:(G)) | idtac "SSR	paper.ex2g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + (X + _) + _); elpi z_report "paper.ex2g" "48" ltac_term:(G)) | idtac "SSR	paper.ex2g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _ = _); elpi z_report "paper.ex2g" "49" ltac_term:(G)) | idtac "SSR	paper.ex2g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + (X + _) + _ = _); elpi z_report "paper.ex2g" "50" ltac_term:(G)) | idtac "SSR	paper.ex2g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ * _); elpi z_report "paper.ex2g" "51" ltac_term:(G)) | idtac "SSR	paper.ex2g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ * _ as X in X + _); elpi z_report "paper.ex2g" "52" ltac_term:(G)) | idtac "SSR	paper.ex2g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b * c); elpi z_report "paper.ex2g" "53" ltac_term:(G)) | idtac "SSR	paper.ex2g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex2g" "54" ltac_term:(G)) | idtac "SSR	paper.ex2g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex2g" "55" ltac_term:(G)) | idtac "SSR	paper.ex2g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X * _ + _)); elpi z_report "paper.ex2g" "56" ltac_term:(G)) | idtac "SSR	paper.ex2g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X * _ + _) + _); elpi z_report "paper.ex2g" "57" ltac_term:(G)) | idtac "SSR	paper.ex2g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X * _ + _) + _ = _); elpi z_report "paper.ex2g" "58" ltac_term:(G)) | idtac "SSR	paper.ex2g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex2g" "59" ltac_term:(G)) | idtac "SSR	paper.ex2g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex2g" "60" ltac_term:(G)) | idtac "SSR	paper.ex2g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X * _); elpi z_report "paper.ex2g" "61" ltac_term:(G)) | idtac "SSR	paper.ex2g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X * _ + _); elpi z_report "paper.ex2g" "62" ltac_term:(G)) | idtac "SSR	paper.ex2g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ * X + _)); elpi z_report "paper.ex2g" "63" ltac_term:(G)) | idtac "SSR	paper.ex2g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ * X + _) + _); elpi z_report "paper.ex2g" "64" ltac_term:(G)) | idtac "SSR	paper.ex2g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ * X + _) + _ = _); elpi z_report "paper.ex2g" "65" ltac_term:(G)) | idtac "SSR	paper.ex2g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex2g" "66" ltac_term:(G)) | idtac "SSR	paper.ex2g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex2g" "67" ltac_term:(G)) | idtac "SSR	paper.ex2g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ * X); elpi z_report "paper.ex2g" "68" ltac_term:(G)) | idtac "SSR	paper.ex2g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ * X + _); elpi z_report "paper.ex2g" "69" ltac_term:(G)) | idtac "SSR	paper.ex2g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "paper.ex2g" "70" ltac_term:(G)) | idtac "SSR	paper.ex2g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _); elpi z_report "paper.ex2g" "71" ltac_term:(G)) | idtac "SSR	paper.ex2g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _ = _); elpi z_report "paper.ex2g" "72" ltac_term:(G)) | idtac "SSR	paper.ex2g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex2g" "73" ltac_term:(G)) | idtac "SSR	paper.ex2g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex2g" "74" ltac_term:(G)) | idtac "SSR	paper.ex2g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in b * c + X); elpi z_report "paper.ex2g" "75" ltac_term:(G)) | idtac "SSR	paper.ex2g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex2g" "76" ltac_term:(G)) | idtac "SSR	paper.ex2g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.ex2g" "77" ltac_term:(G)) | idtac "SSR	paper.ex2g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex2g" "78" ltac_term:(G)) | idtac "SSR	paper.ex2g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex2g" "79" ltac_term:(G)) | idtac "SSR	paper.ex2g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex2g" "80" ltac_term:(G)) | idtac "SSR	paper.ex2g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "paper.ex2g" "81" ltac_term:(G)) | idtac "SSR	paper.ex2g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b * c + _); elpi z_report "paper.ex2g" "82" ltac_term:(G)) | idtac "SSR	paper.ex2g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b * c + _); elpi z_report "paper.ex2g" "83" ltac_term:(G)) | idtac "SSR	paper.ex2g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b * c + a); elpi z_report "paper.ex2g" "84" ltac_term:(G)) | idtac "SSR	paper.ex2g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (add); elpi z_report "paper.ex2g" "85" ltac_term:(G)) | idtac "SSR	paper.ex2g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex2g" "86" ltac_term:(G)) | idtac "SSR	paper.ex2g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex2g" "87" ltac_term:(G)) | idtac "SSR	paper.ex2g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ = X); elpi z_report "paper.ex2g" "88" ltac_term:(G)) | idtac "SSR	paper.ex2g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "paper.ex2g" "89" ltac_term:(G)) | idtac "SSR	paper.ex2g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ = X + _); elpi z_report "paper.ex2g" "90" ltac_term:(G)) | idtac "SSR	paper.ex2g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "paper.ex2g" "91" ltac_term:(G)) | idtac "SSR	paper.ex2g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in X + _); elpi z_report "paper.ex2g" "92" ltac_term:(G)) | idtac "SSR	paper.ex2g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ * _); elpi z_report "paper.ex2g" "93" ltac_term:(G)) | idtac "SSR	paper.ex2g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ * _ as X in X + _); elpi z_report "paper.ex2g" "94" ltac_term:(G)) | idtac "SSR	paper.ex2g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b * c); elpi z_report "paper.ex2g" "95" ltac_term:(G)) | idtac "SSR	paper.ex2g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mul); elpi z_report "paper.ex2g" "96" ltac_term:(G)) | idtac "SSR	paper.ex2g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex2g" "97" ltac_term:(G)) | idtac "SSR	paper.ex2g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex2g" "98" ltac_term:(G)) | idtac "SSR	paper.ex2g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X * _ + _); elpi z_report "paper.ex2g" "99" ltac_term:(G)) | idtac "SSR	paper.ex2g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "paper.ex2g" "100" ltac_term:(G)) | idtac "SSR	paper.ex2g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "paper.ex2g" "101" ltac_term:(G)) | idtac "SSR	paper.ex2g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _ + _); elpi z_report "paper.ex2g" "102" ltac_term:(G)) | idtac "SSR	paper.ex2g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex2g" "103" ltac_term:(G)) | idtac "SSR	paper.ex2g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex2g" "104" ltac_term:(G)) | idtac "SSR	paper.ex2g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X * _); elpi z_report "paper.ex2g" "105" ltac_term:(G)) | idtac "SSR	paper.ex2g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X * _ + _); elpi z_report "paper.ex2g" "106" ltac_term:(G)) | idtac "SSR	paper.ex2g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ * X + _); elpi z_report "paper.ex2g" "107" ltac_term:(G)) | idtac "SSR	paper.ex2g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "paper.ex2g" "108" ltac_term:(G)) | idtac "SSR	paper.ex2g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "paper.ex2g" "109" ltac_term:(G)) | idtac "SSR	paper.ex2g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X + _); elpi z_report "paper.ex2g" "110" ltac_term:(G)) | idtac "SSR	paper.ex2g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "paper.ex2g" "111" ltac_term:(G)) | idtac "SSR	paper.ex2g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "paper.ex2g" "112" ltac_term:(G)) | idtac "SSR	paper.ex2g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ * X); elpi z_report "paper.ex2g" "113" ltac_term:(G)) | idtac "SSR	paper.ex2g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ * X + _); elpi z_report "paper.ex2g" "114" ltac_term:(G)) | idtac "SSR	paper.ex2g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "paper.ex2g" "115" ltac_term:(G)) | idtac "SSR	paper.ex2g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "paper.ex2g" "116" ltac_term:(G)) | idtac "SSR	paper.ex2g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b * c + X); elpi z_report "paper.ex2g" "117" ltac_term:(G)) | idtac "SSR	paper.ex2g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "paper.ex2g" "118" ltac_term:(G)) | idtac "SSR	paper.ex2g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(a); elpi z_report "paper.ex2g" "119" ltac_term:(G)) | idtac "SSR	paper.ex2g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in b * c + X); elpi z_report "paper.ex2g" "120" ltac_term:(G)) | idtac "SSR	paper.ex2g	120	error" ].
Abort.

Goal forall a b c d : R, (a - b) + (b - c) = (a - b) + (d - b).
intros a b c d.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - b); elpi z_report "paper.ex5" "1" ltac_term:(G)) | idtac "SSR	paper.ex5	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ - b); elpi z_report "paper.ex5" "2" ltac_term:(G)) | idtac "SSR	paper.ex5	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1 2}(_ - b); elpi z_report "paper.ex5" "3" ltac_term:(G)) | idtac "SSR	paper.ex5	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {-1}(_ - b); elpi z_report "paper.ex5" "4" ltac_term:(G)) | idtac "SSR	paper.ex5	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(_ - b); elpi z_report "paper.ex5" "5" ltac_term:(G)) | idtac "SSR	paper.ex5	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex5g" "1" ltac_term:(G)) | idtac "SSR	paper.ex5g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a - b + (b - c) = a - b + (d - b)); elpi z_report "paper.ex5g" "2" ltac_term:(G)) | idtac "SSR	paper.ex5g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex5g" "3" ltac_term:(G)) | idtac "SSR	paper.ex5g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex5g" "4" ltac_term:(G)) | idtac "SSR	paper.ex5g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (R); elpi z_report "paper.ex5g" "5" ltac_term:(G)) | idtac "SSR	paper.ex5g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex5g" "6" ltac_term:(G)) | idtac "SSR	paper.ex5g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex5g" "7" ltac_term:(G)) | idtac "SSR	paper.ex5g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex5g" "8" ltac_term:(G)) | idtac "SSR	paper.ex5g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.ex5g" "9" ltac_term:(G)) | idtac "SSR	paper.ex5g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a - b + (b - c)); elpi z_report "paper.ex5g" "10" ltac_term:(G)) | idtac "SSR	paper.ex5g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex5g" "11" ltac_term:(G)) | idtac "SSR	paper.ex5g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex5g" "12" ltac_term:(G)) | idtac "SSR	paper.ex5g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex5g" "13" ltac_term:(G)) | idtac "SSR	paper.ex5g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "paper.ex5g" "14" ltac_term:(G)) | idtac "SSR	paper.ex5g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.ex5g" "15" ltac_term:(G)) | idtac "SSR	paper.ex5g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X = _); elpi z_report "paper.ex5g" "16" ltac_term:(G)) | idtac "SSR	paper.ex5g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "paper.ex5g" "17" ltac_term:(G)) | idtac "SSR	paper.ex5g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + _); elpi z_report "paper.ex5g" "18" ltac_term:(G)) | idtac "SSR	paper.ex5g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a - b); elpi z_report "paper.ex5g" "19" ltac_term:(G)) | idtac "SSR	paper.ex5g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex5g" "20" ltac_term:(G)) | idtac "SSR	paper.ex5g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex5g" "21" ltac_term:(G)) | idtac "SSR	paper.ex5g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "paper.ex5g" "22" ltac_term:(G)) | idtac "SSR	paper.ex5g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "paper.ex5g" "23" ltac_term:(G)) | idtac "SSR	paper.ex5g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex5g" "24" ltac_term:(G)) | idtac "SSR	paper.ex5g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex5g" "25" ltac_term:(G)) | idtac "SSR	paper.ex5g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X - b); elpi z_report "paper.ex5g" "26" ltac_term:(G)) | idtac "SSR	paper.ex5g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in X = _); elpi z_report "paper.ex5g" "27" ltac_term:(G)) | idtac "SSR	paper.ex5g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in X + _); elpi z_report "paper.ex5g" "28" ltac_term:(G)) | idtac "SSR	paper.ex5g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "paper.ex5g" "29" ltac_term:(G)) | idtac "SSR	paper.ex5g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + X + _); elpi z_report "paper.ex5g" "30" ltac_term:(G)) | idtac "SSR	paper.ex5g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in X + _ = _); elpi z_report "paper.ex5g" "31" ltac_term:(G)) | idtac "SSR	paper.ex5g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "paper.ex5g" "32" ltac_term:(G)) | idtac "SSR	paper.ex5g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + X + _ = _); elpi z_report "paper.ex5g" "33" ltac_term:(G)) | idtac "SSR	paper.ex5g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _); elpi z_report "paper.ex5g" "34" ltac_term:(G)) | idtac "SSR	paper.ex5g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + X); elpi z_report "paper.ex5g" "35" ltac_term:(G)) | idtac "SSR	paper.ex5g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(- _); elpi z_report "paper.ex5g" "36" ltac_term:(G)) | idtac "SSR	paper.ex5g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(- b); elpi z_report "paper.ex5g" "37" ltac_term:(G)) | idtac "SSR	paper.ex5g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in a + X); elpi z_report "paper.ex5g" "38" ltac_term:(G)) | idtac "SSR	paper.ex5g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(- _ as X in _ + X); elpi z_report "paper.ex5g" "39" ltac_term:(G)) | idtac "SSR	paper.ex5g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(opp); elpi z_report "paper.ex5g" "40" ltac_term:(G)) | idtac "SSR	paper.ex5g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(opp); elpi z_report "paper.ex5g" "41" ltac_term:(G)) | idtac "SSR	paper.ex5g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ - X + _); elpi z_report "paper.ex5g" "42" ltac_term:(G)) | idtac "SSR	paper.ex5g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ - X + _ = _); elpi z_report "paper.ex5g" "43" ltac_term:(G)) | idtac "SSR	paper.ex5g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in - X); elpi z_report "paper.ex5g" "44" ltac_term:(G)) | idtac "SSR	paper.ex5g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ - X); elpi z_report "paper.ex5g" "45" ltac_term:(G)) | idtac "SSR	paper.ex5g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex5g" "46" ltac_term:(G)) | idtac "SSR	paper.ex5g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex5g" "47" ltac_term:(G)) | idtac "SSR	paper.ex5g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in - X); elpi z_report "paper.ex5g" "48" ltac_term:(G)) | idtac "SSR	paper.ex5g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in _ - X); elpi z_report "paper.ex5g" "49" ltac_term:(G)) | idtac "SSR	paper.ex5g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex5g" "50" ltac_term:(G)) | idtac "SSR	paper.ex5g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _); elpi z_report "paper.ex5g" "51" ltac_term:(G)) | idtac "SSR	paper.ex5g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "paper.ex5g" "52" ltac_term:(G)) | idtac "SSR	paper.ex5g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.ex5g" "53" ltac_term:(G)) | idtac "SSR	paper.ex5g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b + _ in X in X = _); elpi z_report "paper.ex5g" "54" ltac_term:(G)) | idtac "SSR	paper.ex5g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X = _); elpi z_report "paper.ex5g" "55" ltac_term:(G)) | idtac "SSR	paper.ex5g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b - c); elpi z_report "paper.ex5g" "56" ltac_term:(G)) | idtac "SSR	paper.ex5g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex5g" "57" ltac_term:(G)) | idtac "SSR	paper.ex5g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex5g" "58" ltac_term:(G)) | idtac "SSR	paper.ex5g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X - c); elpi z_report "paper.ex5g" "59" ltac_term:(G)) | idtac "SSR	paper.ex5g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "paper.ex5g" "60" ltac_term:(G)) | idtac "SSR	paper.ex5g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) = _); elpi z_report "paper.ex5g" "61" ltac_term:(G)) | idtac "SSR	paper.ex5g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex5g" "62" ltac_term:(G)) | idtac "SSR	paper.ex5g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex5g" "63" ltac_term:(G)) | idtac "SSR	paper.ex5g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- c); elpi z_report "paper.ex5g" "64" ltac_term:(G)) | idtac "SSR	paper.ex5g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b + X); elpi z_report "paper.ex5g" "65" ltac_term:(G)) | idtac "SSR	paper.ex5g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in _ + X); elpi z_report "paper.ex5g" "66" ltac_term:(G)) | idtac "SSR	paper.ex5g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "paper.ex5g" "67" ltac_term:(G)) | idtac "SSR	paper.ex5g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in b + X); elpi z_report "paper.ex5g" "68" ltac_term:(G)) | idtac "SSR	paper.ex5g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- c in X in X = _); elpi z_report "paper.ex5g" "69" ltac_term:(G)) | idtac "SSR	paper.ex5g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in _ + X = _); elpi z_report "paper.ex5g" "70" ltac_term:(G)) | idtac "SSR	paper.ex5g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + (_ + X)); elpi z_report "paper.ex5g" "71" ltac_term:(G)) | idtac "SSR	paper.ex5g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) = _); elpi z_report "paper.ex5g" "72" ltac_term:(G)) | idtac "SSR	paper.ex5g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + (_ + X) = _); elpi z_report "paper.ex5g" "73" ltac_term:(G)) | idtac "SSR	paper.ex5g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(- c); elpi z_report "paper.ex5g" "74" ltac_term:(G)) | idtac "SSR	paper.ex5g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(opp); elpi z_report "paper.ex5g" "75" ltac_term:(G)) | idtac "SSR	paper.ex5g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(opp); elpi z_report "paper.ex5g" "76" ltac_term:(G)) | idtac "SSR	paper.ex5g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "paper.ex5g" "77" ltac_term:(G)) | idtac "SSR	paper.ex5g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in b - X); elpi z_report "paper.ex5g" "78" ltac_term:(G)) | idtac "SSR	paper.ex5g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ - X)); elpi z_report "paper.ex5g" "79" ltac_term:(G)) | idtac "SSR	paper.ex5g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ - X) = _); elpi z_report "paper.ex5g" "80" ltac_term:(G)) | idtac "SSR	paper.ex5g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex5g" "81" ltac_term:(G)) | idtac "SSR	paper.ex5g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex5g" "82" ltac_term:(G)) | idtac "SSR	paper.ex5g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "paper.ex5g" "83" ltac_term:(G)) | idtac "SSR	paper.ex5g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (d + _)); elpi z_report "paper.ex5g" "84" ltac_term:(G)) | idtac "SSR	paper.ex5g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a - b + (d - b)); elpi z_report "paper.ex5g" "85" ltac_term:(G)) | idtac "SSR	paper.ex5g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex5g" "86" ltac_term:(G)) | idtac "SSR	paper.ex5g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex5g" "87" ltac_term:(G)) | idtac "SSR	paper.ex5g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "paper.ex5g" "88" ltac_term:(G)) | idtac "SSR	paper.ex5g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (d + _)); elpi z_report "paper.ex5g" "89" ltac_term:(G)) | idtac "SSR	paper.ex5g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in _ = X); elpi z_report "paper.ex5g" "90" ltac_term:(G)) | idtac "SSR	paper.ex5g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X + _); elpi z_report "paper.ex5g" "91" ltac_term:(G)) | idtac "SSR	paper.ex5g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + (d + _)); elpi z_report "paper.ex5g" "92" ltac_term:(G)) | idtac "SSR	paper.ex5g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "paper.ex5g" "93" ltac_term:(G)) | idtac "SSR	paper.ex5g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + _); elpi z_report "paper.ex5g" "94" ltac_term:(G)) | idtac "SSR	paper.ex5g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a - b); elpi z_report "paper.ex5g" "95" ltac_term:(G)) | idtac "SSR	paper.ex5g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(add); elpi z_report "paper.ex5g" "96" ltac_term:(G)) | idtac "SSR	paper.ex5g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(add); elpi z_report "paper.ex5g" "97" ltac_term:(G)) | idtac "SSR	paper.ex5g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _ + _); elpi z_report "paper.ex5g" "98" ltac_term:(G)) | idtac "SSR	paper.ex5g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + (d + _)); elpi z_report "paper.ex5g" "99" ltac_term:(G)) | idtac "SSR	paper.ex5g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "paper.ex5g" "100" ltac_term:(G)) | idtac "SSR	paper.ex5g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X - b); elpi z_report "paper.ex5g" "101" ltac_term:(G)) | idtac "SSR	paper.ex5g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex5g" "102" ltac_term:(G)) | idtac "SSR	paper.ex5g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex5g" "103" ltac_term:(G)) | idtac "SSR	paper.ex5g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X - b); elpi z_report "paper.ex5g" "104" ltac_term:(G)) | idtac "SSR	paper.ex5g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in _ = X + _); elpi z_report "paper.ex5g" "105" ltac_term:(G)) | idtac "SSR	paper.ex5g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X + _); elpi z_report "paper.ex5g" "106" ltac_term:(G)) | idtac "SSR	paper.ex5g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in X + (d + _)); elpi z_report "paper.ex5g" "107" ltac_term:(G)) | idtac "SSR	paper.ex5g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + (d + _)); elpi z_report "paper.ex5g" "108" ltac_term:(G)) | idtac "SSR	paper.ex5g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ = _ + X + _); elpi z_report "paper.ex5g" "109" ltac_term:(G)) | idtac "SSR	paper.ex5g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + X + (d + _)); elpi z_report "paper.ex5g" "110" ltac_term:(G)) | idtac "SSR	paper.ex5g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + X); elpi z_report "paper.ex5g" "111" ltac_term:(G)) | idtac "SSR	paper.ex5g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in a + X); elpi z_report "paper.ex5g" "112" ltac_term:(G)) | idtac "SSR	paper.ex5g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(- b); elpi z_report "paper.ex5g" "113" ltac_term:(G)) | idtac "SSR	paper.ex5g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(- b); elpi z_report "paper.ex5g" "114" ltac_term:(G)) | idtac "SSR	paper.ex5g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in a + X); elpi z_report "paper.ex5g" "115" ltac_term:(G)) | idtac "SSR	paper.ex5g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(- _ in X in _ = X); elpi z_report "paper.ex5g" "116" ltac_term:(G)) | idtac "SSR	paper.ex5g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(- _ as X in a + X); elpi z_report "paper.ex5g" "117" ltac_term:(G)) | idtac "SSR	paper.ex5g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(opp); elpi z_report "paper.ex5g" "118" ltac_term:(G)) | idtac "SSR	paper.ex5g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(opp); elpi z_report "paper.ex5g" "119" ltac_term:(G)) | idtac "SSR	paper.ex5g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ - X + _); elpi z_report "paper.ex5g" "120" ltac_term:(G)) | idtac "SSR	paper.ex5g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ - X + (d + _)); elpi z_report "paper.ex5g" "121" ltac_term:(G)) | idtac "SSR	paper.ex5g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a - X); elpi z_report "paper.ex5g" "122" ltac_term:(G)) | idtac "SSR	paper.ex5g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "paper.ex5g" "123" ltac_term:(G)) | idtac "SSR	paper.ex5g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(b); elpi z_report "paper.ex5g" "124" ltac_term:(G)) | idtac "SSR	paper.ex5g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in a - X); elpi z_report "paper.ex5g" "125" ltac_term:(G)) | idtac "SSR	paper.ex5g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (d + _); elpi z_report "paper.ex5g" "126" ltac_term:(G)) | idtac "SSR	paper.ex5g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "paper.ex5g" "127" ltac_term:(G)) | idtac "SSR	paper.ex5g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (d + _ as X in _ + X); elpi z_report "paper.ex5g" "128" ltac_term:(G)) | idtac "SSR	paper.ex5g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (d + _ in X in _ = X); elpi z_report "paper.ex5g" "129" ltac_term:(G)) | idtac "SSR	paper.ex5g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = _ + X); elpi z_report "paper.ex5g" "130" ltac_term:(G)) | idtac "SSR	paper.ex5g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(d - b); elpi z_report "paper.ex5g" "131" ltac_term:(G)) | idtac "SSR	paper.ex5g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (add); elpi z_report "paper.ex5g" "132" ltac_term:(G)) | idtac "SSR	paper.ex5g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(add); elpi z_report "paper.ex5g" "133" ltac_term:(G)) | idtac "SSR	paper.ex5g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(add); elpi z_report "paper.ex5g" "134" ltac_term:(G)) | idtac "SSR	paper.ex5g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (d); elpi z_report "paper.ex5g" "135" ltac_term:(G)) | idtac "SSR	paper.ex5g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X - b)); elpi z_report "paper.ex5g" "136" ltac_term:(G)) | idtac "SSR	paper.ex5g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (X + _)); elpi z_report "paper.ex5g" "137" ltac_term:(G)) | idtac "SSR	paper.ex5g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(d); elpi z_report "paper.ex5g" "138" ltac_term:(G)) | idtac "SSR	paper.ex5g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in d + X); elpi z_report "paper.ex5g" "139" ltac_term:(G)) | idtac "SSR	paper.ex5g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in d + X); elpi z_report "paper.ex5g" "140" ltac_term:(G)) | idtac "SSR	paper.ex5g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (d + X)); elpi z_report "paper.ex5g" "141" ltac_term:(G)) | idtac "SSR	paper.ex5g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in _ = _ + X); elpi z_report "paper.ex5g" "142" ltac_term:(G)) | idtac "SSR	paper.ex5g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ + X)); elpi z_report "paper.ex5g" "143" ltac_term:(G)) | idtac "SSR	paper.ex5g	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + (d + X)); elpi z_report "paper.ex5g" "144" ltac_term:(G)) | idtac "SSR	paper.ex5g	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ = _ + (_ + X)); elpi z_report "paper.ex5g" "145" ltac_term:(G)) | idtac "SSR	paper.ex5g	145	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- b); elpi z_report "paper.ex5g" "146" ltac_term:(G)) | idtac "SSR	paper.ex5g	146	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in _ = X); elpi z_report "paper.ex5g" "147" ltac_term:(G)) | idtac "SSR	paper.ex5g	147	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(- b); elpi z_report "paper.ex5g" "148" ltac_term:(G)) | idtac "SSR	paper.ex5g	148	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(- b); elpi z_report "paper.ex5g" "149" ltac_term:(G)) | idtac "SSR	paper.ex5g	149	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(- _ in X in _ = X); elpi z_report "paper.ex5g" "150" ltac_term:(G)) | idtac "SSR	paper.ex5g	150	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (opp); elpi z_report "paper.ex5g" "151" ltac_term:(G)) | idtac "SSR	paper.ex5g	151	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(opp); elpi z_report "paper.ex5g" "152" ltac_term:(G)) | idtac "SSR	paper.ex5g	152	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(opp); elpi z_report "paper.ex5g" "153" ltac_term:(G)) | idtac "SSR	paper.ex5g	153	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in d - X); elpi z_report "paper.ex5g" "154" ltac_term:(G)) | idtac "SSR	paper.ex5g	154	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (d - X)); elpi z_report "paper.ex5g" "155" ltac_term:(G)) | idtac "SSR	paper.ex5g	155	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ - X)); elpi z_report "paper.ex5g" "156" ltac_term:(G)) | idtac "SSR	paper.ex5g	156	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "paper.ex5g" "157" ltac_term:(G)) | idtac "SSR	paper.ex5g	157	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(b); elpi z_report "paper.ex5g" "158" ltac_term:(G)) | idtac "SSR	paper.ex5g	158	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(b); elpi z_report "paper.ex5g" "159" ltac_term:(G)) | idtac "SSR	paper.ex5g	159	error" ].
Abort.

Goal forall a b c : R, 0 = snd (0 * c, 0 * (a + b)).
intros a b c.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, X)); elpi z_report "paper.ex6" "1" ltac_term:(G)) | idtac "SSR	paper.ex6	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 * _); elpi z_report "paper.ex6" "2" ltac_term:(G)) | idtac "SSR	paper.ex6	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex6g" "1" ltac_term:(G)) | idtac "SSR	paper.ex6g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 = snd (0 * c, 0 * (a + b))); elpi z_report "paper.ex6g" "2" ltac_term:(G)) | idtac "SSR	paper.ex6g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex6g" "3" ltac_term:(G)) | idtac "SSR	paper.ex6g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex6g" "4" ltac_term:(G)) | idtac "SSR	paper.ex6g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex6g" "5" ltac_term:(G)) | idtac "SSR	paper.ex6g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex6g" "6" ltac_term:(G)) | idtac "SSR	paper.ex6g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex6g" "7" ltac_term:(G)) | idtac "SSR	paper.ex6g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "paper.ex6g" "8" ltac_term:(G)) | idtac "SSR	paper.ex6g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "paper.ex6g" "9" ltac_term:(G)) | idtac "SSR	paper.ex6g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (snd _); elpi z_report "paper.ex6g" "10" ltac_term:(G)) | idtac "SSR	paper.ex6g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex6g" "11" ltac_term:(G)) | idtac "SSR	paper.ex6g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (snd _ as X in _ = X); elpi z_report "paper.ex6g" "12" ltac_term:(G)) | idtac "SSR	paper.ex6g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(snd (0 * c, 0 * (a + b))); elpi z_report "paper.ex6g" "13" ltac_term:(G)) | idtac "SSR	paper.ex6g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@snd); elpi z_report "paper.ex6g" "14" ltac_term:(G)) | idtac "SSR	paper.ex6g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@snd); elpi z_report "paper.ex6g" "15" ltac_term:(G)) | idtac "SSR	paper.ex6g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(R); elpi z_report "paper.ex6g" "16" ltac_term:(G)) | idtac "SSR	paper.ex6g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(R); elpi z_report "paper.ex6g" "17" ltac_term:(G)) | idtac "SSR	paper.ex6g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(R); elpi z_report "paper.ex6g" "18" ltac_term:(G)) | idtac "SSR	paper.ex6g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(R); elpi z_report "paper.ex6g" "19" ltac_term:(G)) | idtac "SSR	paper.ex6g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_, _); elpi z_report "paper.ex6g" "20" ltac_term:(G)) | idtac "SSR	paper.ex6g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd X); elpi z_report "paper.ex6g" "21" ltac_term:(G)) | idtac "SSR	paper.ex6g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, _) as X in snd X); elpi z_report "paper.ex6g" "22" ltac_term:(G)) | idtac "SSR	paper.ex6g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, _) in X in _ = X); elpi z_report "paper.ex6g" "23" ltac_term:(G)) | idtac "SSR	paper.ex6g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd X); elpi z_report "paper.ex6g" "24" ltac_term:(G)) | idtac "SSR	paper.ex6g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_, _) as X in _ = snd X); elpi z_report "paper.ex6g" "25" ltac_term:(G)) | idtac "SSR	paper.ex6g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 * c, 0 * (a + b)); elpi z_report "paper.ex6g" "26" ltac_term:(G)) | idtac "SSR	paper.ex6g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@pair); elpi z_report "paper.ex6g" "27" ltac_term:(G)) | idtac "SSR	paper.ex6g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@pair); elpi z_report "paper.ex6g" "28" ltac_term:(G)) | idtac "SSR	paper.ex6g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(R); elpi z_report "paper.ex6g" "29" ltac_term:(G)) | idtac "SSR	paper.ex6g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(R); elpi z_report "paper.ex6g" "30" ltac_term:(G)) | idtac "SSR	paper.ex6g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (R); elpi z_report "paper.ex6g" "31" ltac_term:(G)) | idtac "SSR	paper.ex6g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(R); elpi z_report "paper.ex6g" "32" ltac_term:(G)) | idtac "SSR	paper.ex6g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(R); elpi z_report "paper.ex6g" "33" ltac_term:(G)) | idtac "SSR	paper.ex6g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "paper.ex6g" "34" ltac_term:(G)) | idtac "SSR	paper.ex6g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (X, _)); elpi z_report "paper.ex6g" "35" ltac_term:(G)) | idtac "SSR	paper.ex6g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ = X); elpi z_report "paper.ex6g" "36" ltac_term:(G)) | idtac "SSR	paper.ex6g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in snd X); elpi z_report "paper.ex6g" "37" ltac_term:(G)) | idtac "SSR	paper.ex6g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in (X, _)); elpi z_report "paper.ex6g" "38" ltac_term:(G)) | idtac "SSR	paper.ex6g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (X, _)); elpi z_report "paper.ex6g" "39" ltac_term:(G)) | idtac "SSR	paper.ex6g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ = snd X); elpi z_report "paper.ex6g" "40" ltac_term:(G)) | idtac "SSR	paper.ex6g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in snd (X, _)); elpi z_report "paper.ex6g" "41" ltac_term:(G)) | idtac "SSR	paper.ex6g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (X, _)); elpi z_report "paper.ex6g" "42" ltac_term:(G)) | idtac "SSR	paper.ex6g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ = snd (X, _)); elpi z_report "paper.ex6g" "43" ltac_term:(G)) | idtac "SSR	paper.ex6g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 * c); elpi z_report "paper.ex6g" "44" ltac_term:(G)) | idtac "SSR	paper.ex6g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex6g" "45" ltac_term:(G)) | idtac "SSR	paper.ex6g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex6g" "46" ltac_term:(G)) | idtac "SSR	paper.ex6g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "paper.ex6g" "47" ltac_term:(G)) | idtac "SSR	paper.ex6g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (X * _, _)); elpi z_report "paper.ex6g" "48" ltac_term:(G)) | idtac "SSR	paper.ex6g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (X * _, _)); elpi z_report "paper.ex6g" "49" ltac_term:(G)) | idtac "SSR	paper.ex6g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (X * _, _)); elpi z_report "paper.ex6g" "50" ltac_term:(G)) | idtac "SSR	paper.ex6g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "paper.ex6g" "51" ltac_term:(G)) | idtac "SSR	paper.ex6g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "paper.ex6g" "52" ltac_term:(G)) | idtac "SSR	paper.ex6g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "paper.ex6g" "53" ltac_term:(G)) | idtac "SSR	paper.ex6g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "paper.ex6g" "54" ltac_term:(G)) | idtac "SSR	paper.ex6g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ * X, _)); elpi z_report "paper.ex6g" "55" ltac_term:(G)) | idtac "SSR	paper.ex6g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_ * X, _)); elpi z_report "paper.ex6g" "56" ltac_term:(G)) | idtac "SSR	paper.ex6g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (_ * X, _)); elpi z_report "paper.ex6g" "57" ltac_term:(G)) | idtac "SSR	paper.ex6g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex6g" "58" ltac_term:(G)) | idtac "SSR	paper.ex6g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, X)); elpi z_report "paper.ex6g" "59" ltac_term:(G)) | idtac "SSR	paper.ex6g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in (_, X)); elpi z_report "paper.ex6g" "60" ltac_term:(G)) | idtac "SSR	paper.ex6g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, X)); elpi z_report "paper.ex6g" "61" ltac_term:(G)) | idtac "SSR	paper.ex6g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in snd (_, X)); elpi z_report "paper.ex6g" "62" ltac_term:(G)) | idtac "SSR	paper.ex6g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (_, X)); elpi z_report "paper.ex6g" "63" ltac_term:(G)) | idtac "SSR	paper.ex6g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * (a + b)); elpi z_report "paper.ex6g" "64" ltac_term:(G)) | idtac "SSR	paper.ex6g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ = snd (_, X)); elpi z_report "paper.ex6g" "65" ltac_term:(G)) | idtac "SSR	paper.ex6g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * (a + b) in X in _ = X); elpi z_report "paper.ex6g" "66" ltac_term:(G)) | idtac "SSR	paper.ex6g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * (a + b) in X in snd X); elpi z_report "paper.ex6g" "67" ltac_term:(G)) | idtac "SSR	paper.ex6g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * (a + b) in X in _ = snd X); elpi z_report "paper.ex6g" "68" ltac_term:(G)) | idtac "SSR	paper.ex6g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 * (a + b)); elpi z_report "paper.ex6g" "69" ltac_term:(G)) | idtac "SSR	paper.ex6g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mul); elpi z_report "paper.ex6g" "70" ltac_term:(G)) | idtac "SSR	paper.ex6g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex6g" "71" ltac_term:(G)) | idtac "SSR	paper.ex6g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex6g" "72" ltac_term:(G)) | idtac "SSR	paper.ex6g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, X * _)); elpi z_report "paper.ex6g" "73" ltac_term:(G)) | idtac "SSR	paper.ex6g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, X * _)); elpi z_report "paper.ex6g" "74" ltac_term:(G)) | idtac "SSR	paper.ex6g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * (a + b)); elpi z_report "paper.ex6g" "75" ltac_term:(G)) | idtac "SSR	paper.ex6g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (_, X * _)); elpi z_report "paper.ex6g" "76" ltac_term:(G)) | idtac "SSR	paper.ex6g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "paper.ex6g" "77" ltac_term:(G)) | idtac "SSR	paper.ex6g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "paper.ex6g" "78" ltac_term:(G)) | idtac "SSR	paper.ex6g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "paper.ex6g" "79" ltac_term:(G)) | idtac "SSR	paper.ex6g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex6g" "80" ltac_term:(G)) | idtac "SSR	paper.ex6g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ * X); elpi z_report "paper.ex6g" "81" ltac_term:(G)) | idtac "SSR	paper.ex6g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ = X); elpi z_report "paper.ex6g" "82" ltac_term:(G)) | idtac "SSR	paper.ex6g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in snd X); elpi z_report "paper.ex6g" "83" ltac_term:(G)) | idtac "SSR	paper.ex6g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in (_, X)); elpi z_report "paper.ex6g" "84" ltac_term:(G)) | idtac "SSR	paper.ex6g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, _ * X)); elpi z_report "paper.ex6g" "85" ltac_term:(G)) | idtac "SSR	paper.ex6g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ = snd X); elpi z_report "paper.ex6g" "86" ltac_term:(G)) | idtac "SSR	paper.ex6g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in (_, _ * X)); elpi z_report "paper.ex6g" "87" ltac_term:(G)) | idtac "SSR	paper.ex6g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in snd (_, X)); elpi z_report "paper.ex6g" "88" ltac_term:(G)) | idtac "SSR	paper.ex6g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, _ * X)); elpi z_report "paper.ex6g" "89" ltac_term:(G)) | idtac "SSR	paper.ex6g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in snd (_, _ * X)); elpi z_report "paper.ex6g" "90" ltac_term:(G)) | idtac "SSR	paper.ex6g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (_, _ * X)); elpi z_report "paper.ex6g" "91" ltac_term:(G)) | idtac "SSR	paper.ex6g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = snd (_, _ * X)); elpi z_report "paper.ex6g" "92" ltac_term:(G)) | idtac "SSR	paper.ex6g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "paper.ex6g" "93" ltac_term:(G)) | idtac "SSR	paper.ex6g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (add); elpi z_report "paper.ex6g" "94" ltac_term:(G)) | idtac "SSR	paper.ex6g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex6g" "95" ltac_term:(G)) | idtac "SSR	paper.ex6g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "paper.ex6g" "96" ltac_term:(G)) | idtac "SSR	paper.ex6g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex6g" "97" ltac_term:(G)) | idtac "SSR	paper.ex6g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (X + _)); elpi z_report "paper.ex6g" "98" ltac_term:(G)) | idtac "SSR	paper.ex6g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, _ * (X + _))); elpi z_report "paper.ex6g" "99" ltac_term:(G)) | idtac "SSR	paper.ex6g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, _ * (X + _))); elpi z_report "paper.ex6g" "100" ltac_term:(G)) | idtac "SSR	paper.ex6g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (_, _ * (X + _))); elpi z_report "paper.ex6g" "101" ltac_term:(G)) | idtac "SSR	paper.ex6g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex6g" "102" ltac_term:(G)) | idtac "SSR	paper.ex6g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "paper.ex6g" "103" ltac_term:(G)) | idtac "SSR	paper.ex6g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex6g" "104" ltac_term:(G)) | idtac "SSR	paper.ex6g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (_ + X)); elpi z_report "paper.ex6g" "105" ltac_term:(G)) | idtac "SSR	paper.ex6g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_, _ * (_ + X))); elpi z_report "paper.ex6g" "106" ltac_term:(G)) | idtac "SSR	paper.ex6g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in snd (_, _ * (_ + X))); elpi z_report "paper.ex6g" "107" ltac_term:(G)) | idtac "SSR	paper.ex6g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = snd (_, _ * (_ + X))); elpi z_report "paper.ex6g" "108" ltac_term:(G)) | idtac "SSR	paper.ex6g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex6g" "109" ltac_term:(G)) | idtac "SSR	paper.ex6g	109	error" ].
Abort.

Goal forall a b c : R, a + b = f (a * a + b) - c.
intros a b c.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + b in X in _ = X); elpi z_report "paper.ex7" "1" ltac_term:(G)) | idtac "SSR	paper.ex7	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + b); elpi z_report "paper.ex7" "2" ltac_term:(G)) | idtac "SSR	paper.ex7	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + b in RHS); elpi z_report "paper.ex7" "3" ltac_term:(G)) | idtac "SSR	paper.ex7	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex7g" "1" ltac_term:(G)) | idtac "SSR	paper.ex7g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b = f (a * a + b) - c); elpi z_report "paper.ex7g" "2" ltac_term:(G)) | idtac "SSR	paper.ex7g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex7g" "3" ltac_term:(G)) | idtac "SSR	paper.ex7g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex7g" "4" ltac_term:(G)) | idtac "SSR	paper.ex7g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (R); elpi z_report "paper.ex7g" "5" ltac_term:(G)) | idtac "SSR	paper.ex7g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex7g" "6" ltac_term:(G)) | idtac "SSR	paper.ex7g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex7g" "7" ltac_term:(G)) | idtac "SSR	paper.ex7g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex7g" "8" ltac_term:(G)) | idtac "SSR	paper.ex7g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.ex7g" "9" ltac_term:(G)) | idtac "SSR	paper.ex7g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "paper.ex7g" "10" ltac_term:(G)) | idtac "SSR	paper.ex7g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex7g" "11" ltac_term:(G)) | idtac "SSR	paper.ex7g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex7g" "12" ltac_term:(G)) | idtac "SSR	paper.ex7g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex7g" "13" ltac_term:(G)) | idtac "SSR	paper.ex7g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.ex7g" "14" ltac_term:(G)) | idtac "SSR	paper.ex7g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex7g" "15" ltac_term:(G)) | idtac "SSR	paper.ex7g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex7g" "16" ltac_term:(G)) | idtac "SSR	paper.ex7g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex7g" "17" ltac_term:(G)) | idtac "SSR	paper.ex7g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.ex7g" "18" ltac_term:(G)) | idtac "SSR	paper.ex7g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex7g" "19" ltac_term:(G)) | idtac "SSR	paper.ex7g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex7g" "20" ltac_term:(G)) | idtac "SSR	paper.ex7g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex7g" "21" ltac_term:(G)) | idtac "SSR	paper.ex7g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ - c); elpi z_report "paper.ex7g" "22" ltac_term:(G)) | idtac "SSR	paper.ex7g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "paper.ex7g" "23" ltac_term:(G)) | idtac "SSR	paper.ex7g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (a * a + b) - c); elpi z_report "paper.ex7g" "24" ltac_term:(G)) | idtac "SSR	paper.ex7g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex7g" "25" ltac_term:(G)) | idtac "SSR	paper.ex7g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex7g" "26" ltac_term:(G)) | idtac "SSR	paper.ex7g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _); elpi z_report "paper.ex7g" "27" ltac_term:(G)) | idtac "SSR	paper.ex7g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X - c); elpi z_report "paper.ex7g" "28" ltac_term:(G)) | idtac "SSR	paper.ex7g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in X + _); elpi z_report "paper.ex7g" "29" ltac_term:(G)) | idtac "SSR	paper.ex7g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ in X in _ = X); elpi z_report "paper.ex7g" "30" ltac_term:(G)) | idtac "SSR	paper.ex7g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "paper.ex7g" "31" ltac_term:(G)) | idtac "SSR	paper.ex7g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f _ as X in _ = X + _); elpi z_report "paper.ex7g" "32" ltac_term:(G)) | idtac "SSR	paper.ex7g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f (a * a + b)); elpi z_report "paper.ex7g" "33" ltac_term:(G)) | idtac "SSR	paper.ex7g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f); elpi z_report "paper.ex7g" "34" ltac_term:(G)) | idtac "SSR	paper.ex7g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f); elpi z_report "paper.ex7g" "35" ltac_term:(G)) | idtac "SSR	paper.ex7g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X); elpi z_report "paper.ex7g" "36" ltac_term:(G)) | idtac "SSR	paper.ex7g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X); elpi z_report "paper.ex7g" "37" ltac_term:(G)) | idtac "SSR	paper.ex7g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f X + _); elpi z_report "paper.ex7g" "38" ltac_term:(G)) | idtac "SSR	paper.ex7g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + b in X in _ = X); elpi z_report "paper.ex7g" "39" ltac_term:(G)) | idtac "SSR	paper.ex7g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X - c); elpi z_report "paper.ex7g" "40" ltac_term:(G)) | idtac "SSR	paper.ex7g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f X + _); elpi z_report "paper.ex7g" "41" ltac_term:(G)) | idtac "SSR	paper.ex7g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ = X + _); elpi z_report "paper.ex7g" "42" ltac_term:(G)) | idtac "SSR	paper.ex7g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f X + _); elpi z_report "paper.ex7g" "43" ltac_term:(G)) | idtac "SSR	paper.ex7g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a * a + _); elpi z_report "paper.ex7g" "44" ltac_term:(G)) | idtac "SSR	paper.ex7g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = f X + _); elpi z_report "paper.ex7g" "45" ltac_term:(G)) | idtac "SSR	paper.ex7g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * a + b); elpi z_report "paper.ex7g" "46" ltac_term:(G)) | idtac "SSR	paper.ex7g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (add); elpi z_report "paper.ex7g" "47" ltac_term:(G)) | idtac "SSR	paper.ex7g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex7g" "48" ltac_term:(G)) | idtac "SSR	paper.ex7g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex7g" "49" ltac_term:(G)) | idtac "SSR	paper.ex7g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "paper.ex7g" "50" ltac_term:(G)) | idtac "SSR	paper.ex7g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in f X); elpi z_report "paper.ex7g" "51" ltac_term:(G)) | idtac "SSR	paper.ex7g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in X + _); elpi z_report "paper.ex7g" "52" ltac_term:(G)) | idtac "SSR	paper.ex7g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ = X); elpi z_report "paper.ex7g" "53" ltac_term:(G)) | idtac "SSR	paper.ex7g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X + _)); elpi z_report "paper.ex7g" "54" ltac_term:(G)) | idtac "SSR	paper.ex7g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X - c); elpi z_report "paper.ex7g" "55" ltac_term:(G)) | idtac "SSR	paper.ex7g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in f X + _); elpi z_report "paper.ex7g" "56" ltac_term:(G)) | idtac "SSR	paper.ex7g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in f (X + _)); elpi z_report "paper.ex7g" "57" ltac_term:(G)) | idtac "SSR	paper.ex7g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in _ = X + _); elpi z_report "paper.ex7g" "58" ltac_term:(G)) | idtac "SSR	paper.ex7g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X + _) + _); elpi z_report "paper.ex7g" "59" ltac_term:(G)) | idtac "SSR	paper.ex7g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in f (X + _) + _); elpi z_report "paper.ex7g" "60" ltac_term:(G)) | idtac "SSR	paper.ex7g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (X + _) + _); elpi z_report "paper.ex7g" "61" ltac_term:(G)) | idtac "SSR	paper.ex7g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ = f (X + _) + _); elpi z_report "paper.ex7g" "62" ltac_term:(G)) | idtac "SSR	paper.ex7g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * a); elpi z_report "paper.ex7g" "63" ltac_term:(G)) | idtac "SSR	paper.ex7g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mul); elpi z_report "paper.ex7g" "64" ltac_term:(G)) | idtac "SSR	paper.ex7g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex7g" "65" ltac_term:(G)) | idtac "SSR	paper.ex7g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "paper.ex7g" "66" ltac_term:(G)) | idtac "SSR	paper.ex7g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _ + _); elpi z_report "paper.ex7g" "67" ltac_term:(G)) | idtac "SSR	paper.ex7g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X * _ + _)); elpi z_report "paper.ex7g" "68" ltac_term:(G)) | idtac "SSR	paper.ex7g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (X * _ + _) + _); elpi z_report "paper.ex7g" "69" ltac_term:(G)) | idtac "SSR	paper.ex7g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (X * _ + _) + _); elpi z_report "paper.ex7g" "70" ltac_term:(G)) | idtac "SSR	paper.ex7g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex7g" "71" ltac_term:(G)) | idtac "SSR	paper.ex7g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex7g" "72" ltac_term:(G)) | idtac "SSR	paper.ex7g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "paper.ex7g" "73" ltac_term:(G)) | idtac "SSR	paper.ex7g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X + _); elpi z_report "paper.ex7g" "74" ltac_term:(G)) | idtac "SSR	paper.ex7g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ * X + _)); elpi z_report "paper.ex7g" "75" ltac_term:(G)) | idtac "SSR	paper.ex7g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ * X + _) + _); elpi z_report "paper.ex7g" "76" ltac_term:(G)) | idtac "SSR	paper.ex7g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (_ * X + _) + _); elpi z_report "paper.ex7g" "77" ltac_term:(G)) | idtac "SSR	paper.ex7g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "paper.ex7g" "78" ltac_term:(G)) | idtac "SSR	paper.ex7g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex7g" "79" ltac_term:(G)) | idtac "SSR	paper.ex7g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex7g" "80" ltac_term:(G)) | idtac "SSR	paper.ex7g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X)); elpi z_report "paper.ex7g" "81" ltac_term:(G)) | idtac "SSR	paper.ex7g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (_ + X) + _); elpi z_report "paper.ex7g" "82" ltac_term:(G)) | idtac "SSR	paper.ex7g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a * a + X); elpi z_report "paper.ex7g" "83" ltac_term:(G)) | idtac "SSR	paper.ex7g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = f (_ + X) + _); elpi z_report "paper.ex7g" "84" ltac_term:(G)) | idtac "SSR	paper.ex7g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "paper.ex7g" "85" ltac_term:(G)) | idtac "SSR	paper.ex7g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex7g" "86" ltac_term:(G)) | idtac "SSR	paper.ex7g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex7g" "87" ltac_term:(G)) | idtac "SSR	paper.ex7g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _); elpi z_report "paper.ex7g" "88" ltac_term:(G)) | idtac "SSR	paper.ex7g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ + X); elpi z_report "paper.ex7g" "89" ltac_term:(G)) | idtac "SSR	paper.ex7g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ in X in _ = X); elpi z_report "paper.ex7g" "90" ltac_term:(G)) | idtac "SSR	paper.ex7g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "paper.ex7g" "91" ltac_term:(G)) | idtac "SSR	paper.ex7g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (- _ as X in _ = _ + X); elpi z_report "paper.ex7g" "92" ltac_term:(G)) | idtac "SSR	paper.ex7g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f (a * a + b) + X); elpi z_report "paper.ex7g" "93" ltac_term:(G)) | idtac "SSR	paper.ex7g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(- c); elpi z_report "paper.ex7g" "94" ltac_term:(G)) | idtac "SSR	paper.ex7g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (opp); elpi z_report "paper.ex7g" "95" ltac_term:(G)) | idtac "SSR	paper.ex7g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(opp); elpi z_report "paper.ex7g" "96" ltac_term:(G)) | idtac "SSR	paper.ex7g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "paper.ex7g" "97" ltac_term:(G)) | idtac "SSR	paper.ex7g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in - X); elpi z_report "paper.ex7g" "98" ltac_term:(G)) | idtac "SSR	paper.ex7g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ - X); elpi z_report "paper.ex7g" "99" ltac_term:(G)) | idtac "SSR	paper.ex7g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ - X); elpi z_report "paper.ex7g" "100" ltac_term:(G)) | idtac "SSR	paper.ex7g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex7g" "101" ltac_term:(G)) | idtac "SSR	paper.ex7g	101	error" ].
Abort.

Goal forall a b c d : R, f2 (a + b) (2 * (a + c)) + (c + d) + f2 a (c + d) = 0.
intros a b c d.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + d as X in f2 _ X); elpi z_report "paper.ex8" "1" ltac_term:(G)) | idtac "SSR	paper.ex8	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ X); elpi z_report "paper.ex8" "2" ltac_term:(G)) | idtac "SSR	paper.ex8	2	error" ].
idtac "SSR	paper.ex8	3	not a c-pattern".
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex8g" "1" ltac_term:(G)) | idtac "SSR	paper.ex8g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f2 (a + b) (2 * (a + c)) + (c + d) + f2 a (c + d) = 0); elpi z_report "paper.ex8g" "2" ltac_term:(G)) | idtac "SSR	paper.ex8g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex8g" "3" ltac_term:(G)) | idtac "SSR	paper.ex8g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex8g" "4" ltac_term:(G)) | idtac "SSR	paper.ex8g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (R); elpi z_report "paper.ex8g" "5" ltac_term:(G)) | idtac "SSR	paper.ex8g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex8g" "6" ltac_term:(G)) | idtac "SSR	paper.ex8g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex8g" "7" ltac_term:(G)) | idtac "SSR	paper.ex8g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex8g" "8" ltac_term:(G)) | idtac "SSR	paper.ex8g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.ex8g" "9" ltac_term:(G)) | idtac "SSR	paper.ex8g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f2 (a + b) (2 * (a + c)) + (c + d) + f2 a (c + d)); elpi z_report "paper.ex8g" "10" ltac_term:(G)) | idtac "SSR	paper.ex8g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex8g" "11" ltac_term:(G)) | idtac "SSR	paper.ex8g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex8g" "12" ltac_term:(G)) | idtac "SSR	paper.ex8g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex8g" "13" ltac_term:(G)) | idtac "SSR	paper.ex8g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "paper.ex8g" "14" ltac_term:(G)) | idtac "SSR	paper.ex8g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.ex8g" "15" ltac_term:(G)) | idtac "SSR	paper.ex8g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "paper.ex8g" "16" ltac_term:(G)) | idtac "SSR	paper.ex8g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (c + d)); elpi z_report "paper.ex8g" "17" ltac_term:(G)) | idtac "SSR	paper.ex8g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (c + d) in X in X = _); elpi z_report "paper.ex8g" "18" ltac_term:(G)) | idtac "SSR	paper.ex8g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f2 (a + b) (2 * (a + c)) + (c + d)); elpi z_report "paper.ex8g" "19" ltac_term:(G)) | idtac "SSR	paper.ex8g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex8g" "20" ltac_term:(G)) | idtac "SSR	paper.ex8g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex8g" "21" ltac_term:(G)) | idtac "SSR	paper.ex8g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _); elpi z_report "paper.ex8g" "22" ltac_term:(G)) | idtac "SSR	paper.ex8g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ as X in X + _); elpi z_report "paper.ex8g" "23" ltac_term:(G)) | idtac "SSR	paper.ex8g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ in X in X = _); elpi z_report "paper.ex8g" "24" ltac_term:(G)) | idtac "SSR	paper.ex8g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ in X in X + _); elpi z_report "paper.ex8g" "25" ltac_term:(G)) | idtac "SSR	paper.ex8g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "paper.ex8g" "26" ltac_term:(G)) | idtac "SSR	paper.ex8g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ as X in X + _ + _); elpi z_report "paper.ex8g" "27" ltac_term:(G)) | idtac "SSR	paper.ex8g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ in X in X + _ = _); elpi z_report "paper.ex8g" "28" ltac_term:(G)) | idtac "SSR	paper.ex8g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "paper.ex8g" "29" ltac_term:(G)) | idtac "SSR	paper.ex8g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (c + d)); elpi z_report "paper.ex8g" "30" ltac_term:(G)) | idtac "SSR	paper.ex8g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ as X in X + _ + _ = _); elpi z_report "paper.ex8g" "31" ltac_term:(G)) | idtac "SSR	paper.ex8g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f2 (a + b) (2 * (a + c))); elpi z_report "paper.ex8g" "32" ltac_term:(G)) | idtac "SSR	paper.ex8g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f2); elpi z_report "paper.ex8g" "33" ltac_term:(G)) | idtac "SSR	paper.ex8g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f2); elpi z_report "paper.ex8g" "34" ltac_term:(G)) | idtac "SSR	paper.ex8g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 X _); elpi z_report "paper.ex8g" "35" ltac_term:(G)) | idtac "SSR	paper.ex8g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "paper.ex8g" "36" ltac_term:(G)) | idtac "SSR	paper.ex8g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 X _); elpi z_report "paper.ex8g" "37" ltac_term:(G)) | idtac "SSR	paper.ex8g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 X _ + _); elpi z_report "paper.ex8g" "38" ltac_term:(G)) | idtac "SSR	paper.ex8g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X = _); elpi z_report "paper.ex8g" "39" ltac_term:(G)) | idtac "SSR	paper.ex8g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X + _); elpi z_report "paper.ex8g" "40" ltac_term:(G)) | idtac "SSR	paper.ex8g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X + _ + _); elpi z_report "paper.ex8g" "41" ltac_term:(G)) | idtac "SSR	paper.ex8g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 X _ + _); elpi z_report "paper.ex8g" "42" ltac_term:(G)) | idtac "SSR	paper.ex8g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 X _ + _ + _); elpi z_report "paper.ex8g" "43" ltac_term:(G)) | idtac "SSR	paper.ex8g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X + _ = _); elpi z_report "paper.ex8g" "44" ltac_term:(G)) | idtac "SSR	paper.ex8g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 X _ + _ + _); elpi z_report "paper.ex8g" "45" ltac_term:(G)) | idtac "SSR	paper.ex8g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 X _ + _ + _ = _); elpi z_report "paper.ex8g" "46" ltac_term:(G)) | idtac "SSR	paper.ex8g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in X + (c + d)); elpi z_report "paper.ex8g" "47" ltac_term:(G)) | idtac "SSR	paper.ex8g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 X _ + _ + _ = _); elpi z_report "paper.ex8g" "48" ltac_term:(G)) | idtac "SSR	paper.ex8g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "paper.ex8g" "49" ltac_term:(G)) | idtac "SSR	paper.ex8g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex8g" "50" ltac_term:(G)) | idtac "SSR	paper.ex8g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex8g" "51" ltac_term:(G)) | idtac "SSR	paper.ex8g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + b); elpi z_report "paper.ex8g" "52" ltac_term:(G)) | idtac "SSR	paper.ex8g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (X + _) _); elpi z_report "paper.ex8g" "53" ltac_term:(G)) | idtac "SSR	paper.ex8g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (X + _) _ + _); elpi z_report "paper.ex8g" "54" ltac_term:(G)) | idtac "SSR	paper.ex8g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (X + _) _ + _ + _); elpi z_report "paper.ex8g" "55" ltac_term:(G)) | idtac "SSR	paper.ex8g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (X + _) _ + _ + _ = _); elpi z_report "paper.ex8g" "56" ltac_term:(G)) | idtac "SSR	paper.ex8g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex8g" "57" ltac_term:(G)) | idtac "SSR	paper.ex8g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex8g" "58" ltac_term:(G)) | idtac "SSR	paper.ex8g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "paper.ex8g" "59" ltac_term:(G)) | idtac "SSR	paper.ex8g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + X); elpi z_report "paper.ex8g" "60" ltac_term:(G)) | idtac "SSR	paper.ex8g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (_ + X) _); elpi z_report "paper.ex8g" "61" ltac_term:(G)) | idtac "SSR	paper.ex8g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (_ + X) _ + _); elpi z_report "paper.ex8g" "62" ltac_term:(G)) | idtac "SSR	paper.ex8g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (_ + X) _ + _ + _); elpi z_report "paper.ex8g" "63" ltac_term:(G)) | idtac "SSR	paper.ex8g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (_ + X) _ + _ + _ = _); elpi z_report "paper.ex8g" "64" ltac_term:(G)) | idtac "SSR	paper.ex8g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex8g" "65" ltac_term:(G)) | idtac "SSR	paper.ex8g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "paper.ex8g" "66" ltac_term:(G)) | idtac "SSR	paper.ex8g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ X); elpi z_report "paper.ex8g" "67" ltac_term:(G)) | idtac "SSR	paper.ex8g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _); elpi z_report "paper.ex8g" "68" ltac_term:(G)) | idtac "SSR	paper.ex8g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + _); elpi z_report "paper.ex8g" "69" ltac_term:(G)) | idtac "SSR	paper.ex8g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in f2 _ X); elpi z_report "paper.ex8g" "70" ltac_term:(G)) | idtac "SSR	paper.ex8g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ X + _); elpi z_report "paper.ex8g" "71" ltac_term:(G)) | idtac "SSR	paper.ex8g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + _ = _); elpi z_report "paper.ex8g" "72" ltac_term:(G)) | idtac "SSR	paper.ex8g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + _ + _); elpi z_report "paper.ex8g" "73" ltac_term:(G)) | idtac "SSR	paper.ex8g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in f2 _ X + _); elpi z_report "paper.ex8g" "74" ltac_term:(G)) | idtac "SSR	paper.ex8g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ X + _ + _); elpi z_report "paper.ex8g" "75" ltac_term:(G)) | idtac "SSR	paper.ex8g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in f2 _ X + _ + _); elpi z_report "paper.ex8g" "76" ltac_term:(G)) | idtac "SSR	paper.ex8g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ X + _ + _ = _); elpi z_report "paper.ex8g" "77" ltac_term:(G)) | idtac "SSR	paper.ex8g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X + (c + d)); elpi z_report "paper.ex8g" "78" ltac_term:(G)) | idtac "SSR	paper.ex8g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in f2 _ X + _ + _ = _); elpi z_report "paper.ex8g" "79" ltac_term:(G)) | idtac "SSR	paper.ex8g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 * (a + c)); elpi z_report "paper.ex8g" "80" ltac_term:(G)) | idtac "SSR	paper.ex8g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mul); elpi z_report "paper.ex8g" "81" ltac_term:(G)) | idtac "SSR	paper.ex8g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex8g" "82" ltac_term:(G)) | idtac "SSR	paper.ex8g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (2); elpi z_report "paper.ex8g" "83" ltac_term:(G)) | idtac "SSR	paper.ex8g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "paper.ex8g" "84" ltac_term:(G)) | idtac "SSR	paper.ex8g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (X * _)); elpi z_report "paper.ex8g" "85" ltac_term:(G)) | idtac "SSR	paper.ex8g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (X * _) + _); elpi z_report "paper.ex8g" "86" ltac_term:(G)) | idtac "SSR	paper.ex8g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (X * _) + _ + _); elpi z_report "paper.ex8g" "87" ltac_term:(G)) | idtac "SSR	paper.ex8g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (X * _) + _ + _ = _); elpi z_report "paper.ex8g" "88" ltac_term:(G)) | idtac "SSR	paper.ex8g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2); elpi z_report "paper.ex8g" "89" ltac_term:(G)) | idtac "SSR	paper.ex8g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "paper.ex8g" "90" ltac_term:(G)) | idtac "SSR	paper.ex8g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + c); elpi z_report "paper.ex8g" "91" ltac_term:(G)) | idtac "SSR	paper.ex8g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ * X); elpi z_report "paper.ex8g" "92" ltac_term:(G)) | idtac "SSR	paper.ex8g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in f2 _ X); elpi z_report "paper.ex8g" "93" ltac_term:(G)) | idtac "SSR	paper.ex8g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * X)); elpi z_report "paper.ex8g" "94" ltac_term:(G)) | idtac "SSR	paper.ex8g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + c in X in X + _); elpi z_report "paper.ex8g" "95" ltac_term:(G)) | idtac "SSR	paper.ex8g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in f2 _ X + _); elpi z_report "paper.ex8g" "96" ltac_term:(G)) | idtac "SSR	paper.ex8g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 _ (_ * X)); elpi z_report "paper.ex8g" "97" ltac_term:(G)) | idtac "SSR	paper.ex8g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * X) + _); elpi z_report "paper.ex8g" "98" ltac_term:(G)) | idtac "SSR	paper.ex8g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + c in X in X + _ = _); elpi z_report "paper.ex8g" "99" ltac_term:(G)) | idtac "SSR	paper.ex8g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + c in X in X + _ + _); elpi z_report "paper.ex8g" "100" ltac_term:(G)) | idtac "SSR	paper.ex8g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 _ (_ * X) + _); elpi z_report "paper.ex8g" "101" ltac_term:(G)) | idtac "SSR	paper.ex8g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * X) + _ + _); elpi z_report "paper.ex8g" "102" ltac_term:(G)) | idtac "SSR	paper.ex8g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 _ (_ * X) + _ + _); elpi z_report "paper.ex8g" "103" ltac_term:(G)) | idtac "SSR	paper.ex8g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * X) + _ + _ = _); elpi z_report "paper.ex8g" "104" ltac_term:(G)) | idtac "SSR	paper.ex8g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + c in X in X + (c + d)); elpi z_report "paper.ex8g" "105" ltac_term:(G)) | idtac "SSR	paper.ex8g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 _ (_ * X) + _ + _ = _); elpi z_report "paper.ex8g" "106" ltac_term:(G)) | idtac "SSR	paper.ex8g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + c); elpi z_report "paper.ex8g" "107" ltac_term:(G)) | idtac "SSR	paper.ex8g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex8g" "108" ltac_term:(G)) | idtac "SSR	paper.ex8g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(add); elpi z_report "paper.ex8g" "109" ltac_term:(G)) | idtac "SSR	paper.ex8g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + c); elpi z_report "paper.ex8g" "110" ltac_term:(G)) | idtac "SSR	paper.ex8g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (X + _)); elpi z_report "paper.ex8g" "111" ltac_term:(G)) | idtac "SSR	paper.ex8g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (X + _))); elpi z_report "paper.ex8g" "112" ltac_term:(G)) | idtac "SSR	paper.ex8g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (X + _)) + _); elpi z_report "paper.ex8g" "113" ltac_term:(G)) | idtac "SSR	paper.ex8g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (X + _)) + _ + _); elpi z_report "paper.ex8g" "114" ltac_term:(G)) | idtac "SSR	paper.ex8g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (X + _)) + _ + _ = _); elpi z_report "paper.ex8g" "115" ltac_term:(G)) | idtac "SSR	paper.ex8g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex8g" "116" ltac_term:(G)) | idtac "SSR	paper.ex8g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex8g" "117" ltac_term:(G)) | idtac "SSR	paper.ex8g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (_ + X)); elpi z_report "paper.ex8g" "118" ltac_term:(G)) | idtac "SSR	paper.ex8g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (_ + X))); elpi z_report "paper.ex8g" "119" ltac_term:(G)) | idtac "SSR	paper.ex8g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (_ + X)) + _); elpi z_report "paper.ex8g" "120" ltac_term:(G)) | idtac "SSR	paper.ex8g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (_ + X)) + _ + _); elpi z_report "paper.ex8g" "121" ltac_term:(G)) | idtac "SSR	paper.ex8g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ * (_ + X)) + _ + _ = _); elpi z_report "paper.ex8g" "122" ltac_term:(G)) | idtac "SSR	paper.ex8g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex8g" "123" ltac_term:(G)) | idtac "SSR	paper.ex8g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c); elpi z_report "paper.ex8g" "124" ltac_term:(G)) | idtac "SSR	paper.ex8g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "paper.ex8g" "125" ltac_term:(G)) | idtac "SSR	paper.ex8g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "paper.ex8g" "126" ltac_term:(G)) | idtac "SSR	paper.ex8g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _ in X in X + _); elpi z_report "paper.ex8g" "127" ltac_term:(G)) | idtac "SSR	paper.ex8g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _); elpi z_report "paper.ex8g" "128" ltac_term:(G)) | idtac "SSR	paper.ex8g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "paper.ex8g" "129" ltac_term:(G)) | idtac "SSR	paper.ex8g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _ in X in X + _ = _); elpi z_report "paper.ex8g" "130" ltac_term:(G)) | idtac "SSR	paper.ex8g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _ = _); elpi z_report "paper.ex8g" "131" ltac_term:(G)) | idtac "SSR	paper.ex8g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 (a + b) (2 * (a + c)) + X); elpi z_report "paper.ex8g" "132" ltac_term:(G)) | idtac "SSR	paper.ex8g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c + _); elpi z_report "paper.ex8g" "133" ltac_term:(G)) | idtac "SSR	paper.ex8g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c + d); elpi z_report "paper.ex8g" "134" ltac_term:(G)) | idtac "SSR	paper.ex8g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(c + _ in X in X = _); elpi z_report "paper.ex8g" "135" ltac_term:(G)) | idtac "SSR	paper.ex8g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(add); elpi z_report "paper.ex8g" "136" ltac_term:(G)) | idtac "SSR	paper.ex8g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(add); elpi z_report "paper.ex8g" "137" ltac_term:(G)) | idtac "SSR	paper.ex8g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "paper.ex8g" "138" ltac_term:(G)) | idtac "SSR	paper.ex8g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _); elpi z_report "paper.ex8g" "139" ltac_term:(G)) | idtac "SSR	paper.ex8g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _ = _); elpi z_report "paper.ex8g" "140" ltac_term:(G)) | idtac "SSR	paper.ex8g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "paper.ex8g" "141" ltac_term:(G)) | idtac "SSR	paper.ex8g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c); elpi z_report "paper.ex8g" "142" ltac_term:(G)) | idtac "SSR	paper.ex8g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + d); elpi z_report "paper.ex8g" "143" ltac_term:(G)) | idtac "SSR	paper.ex8g	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "paper.ex8g" "144" ltac_term:(G)) | idtac "SSR	paper.ex8g	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _); elpi z_report "paper.ex8g" "145" ltac_term:(G)) | idtac "SSR	paper.ex8g	145	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _ = _); elpi z_report "paper.ex8g" "146" ltac_term:(G)) | idtac "SSR	paper.ex8g	146	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(d); elpi z_report "paper.ex8g" "147" ltac_term:(G)) | idtac "SSR	paper.ex8g	147	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(d); elpi z_report "paper.ex8g" "148" ltac_term:(G)) | idtac "SSR	paper.ex8g	148	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in c + X); elpi z_report "paper.ex8g" "149" ltac_term:(G)) | idtac "SSR	paper.ex8g	149	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex8g" "150" ltac_term:(G)) | idtac "SSR	paper.ex8g	150	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 a _); elpi z_report "paper.ex8g" "151" ltac_term:(G)) | idtac "SSR	paper.ex8g	151	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ as X in _ + X); elpi z_report "paper.ex8g" "152" ltac_term:(G)) | idtac "SSR	paper.ex8g	152	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.ex8g" "153" ltac_term:(G)) | idtac "SSR	paper.ex8g	153	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 a _ in X in X = _); elpi z_report "paper.ex8g" "154" ltac_term:(G)) | idtac "SSR	paper.ex8g	154	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2 _ _ as X in _ + X = _); elpi z_report "paper.ex8g" "155" ltac_term:(G)) | idtac "SSR	paper.ex8g	155	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f2 a (c + d)); elpi z_report "paper.ex8g" "156" ltac_term:(G)) | idtac "SSR	paper.ex8g	156	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f2); elpi z_report "paper.ex8g" "157" ltac_term:(G)) | idtac "SSR	paper.ex8g	157	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(f2); elpi z_report "paper.ex8g" "158" ltac_term:(G)) | idtac "SSR	paper.ex8g	158	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(f2); elpi z_report "paper.ex8g" "159" ltac_term:(G)) | idtac "SSR	paper.ex8g	159	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 X _); elpi z_report "paper.ex8g" "160" ltac_term:(G)) | idtac "SSR	paper.ex8g	160	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 X _ = _); elpi z_report "paper.ex8g" "161" ltac_term:(G)) | idtac "SSR	paper.ex8g	161	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 X (c + d)); elpi z_report "paper.ex8g" "162" ltac_term:(G)) | idtac "SSR	paper.ex8g	162	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "paper.ex8g" "163" ltac_term:(G)) | idtac "SSR	paper.ex8g	163	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex8g" "164" ltac_term:(G)) | idtac "SSR	paper.ex8g	164	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex8g" "165" ltac_term:(G)) | idtac "SSR	paper.ex8g	165	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 a X); elpi z_report "paper.ex8g" "166" ltac_term:(G)) | idtac "SSR	paper.ex8g	166	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ + X); elpi z_report "paper.ex8g" "167" ltac_term:(G)) | idtac "SSR	paper.ex8g	167	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in f2 _ X); elpi z_report "paper.ex8g" "168" ltac_term:(G)) | idtac "SSR	paper.ex8g	168	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 _ X); elpi z_report "paper.ex8g" "169" ltac_term:(G)) | idtac "SSR	paper.ex8g	169	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ + X = _); elpi z_report "paper.ex8g" "170" ltac_term:(G)) | idtac "SSR	paper.ex8g	170	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + f2 _ X); elpi z_report "paper.ex8g" "171" ltac_term:(G)) | idtac "SSR	paper.ex8g	171	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 _ X = _); elpi z_report "paper.ex8g" "172" ltac_term:(G)) | idtac "SSR	paper.ex8g	172	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + f2 _ X = _); elpi z_report "paper.ex8g" "173" ltac_term:(G)) | idtac "SSR	paper.ex8g	173	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _); elpi z_report "paper.ex8g" "174" ltac_term:(G)) | idtac "SSR	paper.ex8g	174	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c + _ in X in X = _); elpi z_report "paper.ex8g" "175" ltac_term:(G)) | idtac "SSR	paper.ex8g	175	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c + _); elpi z_report "paper.ex8g" "176" ltac_term:(G)) | idtac "SSR	paper.ex8g	176	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c + d); elpi z_report "paper.ex8g" "177" ltac_term:(G)) | idtac "SSR	paper.ex8g	177	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(c + _ in X in X = _); elpi z_report "paper.ex8g" "178" ltac_term:(G)) | idtac "SSR	paper.ex8g	178	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (add); elpi z_report "paper.ex8g" "179" ltac_term:(G)) | idtac "SSR	paper.ex8g	179	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(add); elpi z_report "paper.ex8g" "180" ltac_term:(G)) | idtac "SSR	paper.ex8g	180	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(add); elpi z_report "paper.ex8g" "181" ltac_term:(G)) | idtac "SSR	paper.ex8g	181	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (X + _)); elpi z_report "paper.ex8g" "182" ltac_term:(G)) | idtac "SSR	paper.ex8g	182	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 _ (X + _)); elpi z_report "paper.ex8g" "183" ltac_term:(G)) | idtac "SSR	paper.ex8g	183	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 _ (X + _) = _); elpi z_report "paper.ex8g" "184" ltac_term:(G)) | idtac "SSR	paper.ex8g	184	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (c); elpi z_report "paper.ex8g" "185" ltac_term:(G)) | idtac "SSR	paper.ex8g	185	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + d); elpi z_report "paper.ex8g" "186" ltac_term:(G)) | idtac "SSR	paper.ex8g	186	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(c); elpi z_report "paper.ex8g" "187" ltac_term:(G)) | idtac "SSR	paper.ex8g	187	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(c); elpi z_report "paper.ex8g" "188" ltac_term:(G)) | idtac "SSR	paper.ex8g	188	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X + d); elpi z_report "paper.ex8g" "189" ltac_term:(G)) | idtac "SSR	paper.ex8g	189	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in f2 _ (_ + X)); elpi z_report "paper.ex8g" "190" ltac_term:(G)) | idtac "SSR	paper.ex8g	190	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 _ (_ + X)); elpi z_report "paper.ex8g" "191" ltac_term:(G)) | idtac "SSR	paper.ex8g	191	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + f2 _ (_ + X) = _); elpi z_report "paper.ex8g" "192" ltac_term:(G)) | idtac "SSR	paper.ex8g	192	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (d); elpi z_report "paper.ex8g" "193" ltac_term:(G)) | idtac "SSR	paper.ex8g	193	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in c + X); elpi z_report "paper.ex8g" "194" ltac_term:(G)) | idtac "SSR	paper.ex8g	194	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(d); elpi z_report "paper.ex8g" "195" ltac_term:(G)) | idtac "SSR	paper.ex8g	195	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(d); elpi z_report "paper.ex8g" "196" ltac_term:(G)) | idtac "SSR	paper.ex8g	196	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in c + X); elpi z_report "paper.ex8g" "197" ltac_term:(G)) | idtac "SSR	paper.ex8g	197	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "paper.ex8g" "198" ltac_term:(G)) | idtac "SSR	paper.ex8g	198	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex8g" "199" ltac_term:(G)) | idtac "SSR	paper.ex8g	199	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "paper.ex8g" "200" ltac_term:(G)) | idtac "SSR	paper.ex8g	200	error" ].
Abort.

Goal forall a b d : R, a + b + (a * ((a + b) * d)) = 0.
intros a b d.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := ((_ + _) in X in (_ * X)); elpi z_report "paper.ex9" "1" ltac_term:(G)) | idtac "SSR	paper.ex9	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex9" "2" ltac_term:(G)) | idtac "SSR	paper.ex9	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex9g" "1" ltac_term:(G)) | idtac "SSR	paper.ex9g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b + a * ((a + b) * d) = 0); elpi z_report "paper.ex9g" "2" ltac_term:(G)) | idtac "SSR	paper.ex9g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex9g" "3" ltac_term:(G)) | idtac "SSR	paper.ex9g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex9g" "4" ltac_term:(G)) | idtac "SSR	paper.ex9g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (R); elpi z_report "paper.ex9g" "5" ltac_term:(G)) | idtac "SSR	paper.ex9g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(R); elpi z_report "paper.ex9g" "6" ltac_term:(G)) | idtac "SSR	paper.ex9g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex9g" "7" ltac_term:(G)) | idtac "SSR	paper.ex9g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex9g" "8" ltac_term:(G)) | idtac "SSR	paper.ex9g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.ex9g" "9" ltac_term:(G)) | idtac "SSR	paper.ex9g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b + a * ((a + b) * d)); elpi z_report "paper.ex9g" "10" ltac_term:(G)) | idtac "SSR	paper.ex9g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex9g" "11" ltac_term:(G)) | idtac "SSR	paper.ex9g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(add); elpi z_report "paper.ex9g" "12" ltac_term:(G)) | idtac "SSR	paper.ex9g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex9g" "13" ltac_term:(G)) | idtac "SSR	paper.ex9g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "paper.ex9g" "14" ltac_term:(G)) | idtac "SSR	paper.ex9g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.ex9g" "15" ltac_term:(G)) | idtac "SSR	paper.ex9g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "paper.ex9g" "16" ltac_term:(G)) | idtac "SSR	paper.ex9g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + _); elpi z_report "paper.ex9g" "17" ltac_term:(G)) | idtac "SSR	paper.ex9g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + b); elpi z_report "paper.ex9g" "18" ltac_term:(G)) | idtac "SSR	paper.ex9g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a + _ in X in X = _); elpi z_report "paper.ex9g" "19" ltac_term:(G)) | idtac "SSR	paper.ex9g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex9g" "20" ltac_term:(G)) | idtac "SSR	paper.ex9g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(add); elpi z_report "paper.ex9g" "21" ltac_term:(G)) | idtac "SSR	paper.ex9g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "paper.ex9g" "22" ltac_term:(G)) | idtac "SSR	paper.ex9g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "paper.ex9g" "23" ltac_term:(G)) | idtac "SSR	paper.ex9g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex9g" "24" ltac_term:(G)) | idtac "SSR	paper.ex9g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a); elpi z_report "paper.ex9g" "25" ltac_term:(G)) | idtac "SSR	paper.ex9g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + b); elpi z_report "paper.ex9g" "26" ltac_term:(G)) | idtac "SSR	paper.ex9g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "paper.ex9g" "27" ltac_term:(G)) | idtac "SSR	paper.ex9g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "paper.ex9g" "28" ltac_term:(G)) | idtac "SSR	paper.ex9g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex9g" "29" ltac_term:(G)) | idtac "SSR	paper.ex9g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(b); elpi z_report "paper.ex9g" "30" ltac_term:(G)) | idtac "SSR	paper.ex9g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in a + X); elpi z_report "paper.ex9g" "31" ltac_term:(G)) | idtac "SSR	paper.ex9g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "paper.ex9g" "32" ltac_term:(G)) | idtac "SSR	paper.ex9g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex9g" "33" ltac_term:(G)) | idtac "SSR	paper.ex9g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X); elpi z_report "paper.ex9g" "34" ltac_term:(G)) | idtac "SSR	paper.ex9g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _); elpi z_report "paper.ex9g" "35" ltac_term:(G)) | idtac "SSR	paper.ex9g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.ex9g" "36" ltac_term:(G)) | idtac "SSR	paper.ex9g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X = _); elpi z_report "paper.ex9g" "37" ltac_term:(G)) | idtac "SSR	paper.ex9g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(a * ((a + b) * d)); elpi z_report "paper.ex9g" "38" ltac_term:(G)) | idtac "SSR	paper.ex9g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex9g" "39" ltac_term:(G)) | idtac "SSR	paper.ex9g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(mul); elpi z_report "paper.ex9g" "40" ltac_term:(G)) | idtac "SSR	paper.ex9g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "paper.ex9g" "41" ltac_term:(G)) | idtac "SSR	paper.ex9g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _); elpi z_report "paper.ex9g" "42" ltac_term:(G)) | idtac "SSR	paper.ex9g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _ = _); elpi z_report "paper.ex9g" "43" ltac_term:(G)) | idtac "SSR	paper.ex9g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex9g" "44" ltac_term:(G)) | idtac "SSR	paper.ex9g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a); elpi z_report "paper.ex9g" "45" ltac_term:(G)) | idtac "SSR	paper.ex9g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "paper.ex9g" "46" ltac_term:(G)) | idtac "SSR	paper.ex9g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * d); elpi z_report "paper.ex9g" "47" ltac_term:(G)) | idtac "SSR	paper.ex9g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ * X); elpi z_report "paper.ex9g" "48" ltac_term:(G)) | idtac "SSR	paper.ex9g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X); elpi z_report "paper.ex9g" "49" ltac_term:(G)) | idtac "SSR	paper.ex9g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * d in X in X = _); elpi z_report "paper.ex9g" "50" ltac_term:(G)) | idtac "SSR	paper.ex9g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * d in X in _ + X); elpi z_report "paper.ex9g" "51" ltac_term:(G)) | idtac "SSR	paper.ex9g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + _ * X); elpi z_report "paper.ex9g" "52" ltac_term:(G)) | idtac "SSR	paper.ex9g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X = _); elpi z_report "paper.ex9g" "53" ltac_term:(G)) | idtac "SSR	paper.ex9g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * d in X in _ + X = _); elpi z_report "paper.ex9g" "54" ltac_term:(G)) | idtac "SSR	paper.ex9g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + _ * X = _); elpi z_report "paper.ex9g" "55" ltac_term:(G)) | idtac "SSR	paper.ex9g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}((a + b) * d); elpi z_report "paper.ex9g" "56" ltac_term:(G)) | idtac "SSR	paper.ex9g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (mul); elpi z_report "paper.ex9g" "57" ltac_term:(G)) | idtac "SSR	paper.ex9g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex9g" "58" ltac_term:(G)) | idtac "SSR	paper.ex9g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(mul); elpi z_report "paper.ex9g" "59" ltac_term:(G)) | idtac "SSR	paper.ex9g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * d); elpi z_report "paper.ex9g" "60" ltac_term:(G)) | idtac "SSR	paper.ex9g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X * _); elpi z_report "paper.ex9g" "61" ltac_term:(G)) | idtac "SSR	paper.ex9g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ + X); elpi z_report "paper.ex9g" "62" ltac_term:(G)) | idtac "SSR	paper.ex9g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ * X); elpi z_report "paper.ex9g" "63" ltac_term:(G)) | idtac "SSR	paper.ex9g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (X * _)); elpi z_report "paper.ex9g" "64" ltac_term:(G)) | idtac "SSR	paper.ex9g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ + X = _); elpi z_report "paper.ex9g" "65" ltac_term:(G)) | idtac "SSR	paper.ex9g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ in X in _ + _ * X); elpi z_report "paper.ex9g" "66" ltac_term:(G)) | idtac "SSR	paper.ex9g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ * (X * _)); elpi z_report "paper.ex9g" "67" ltac_term:(G)) | idtac "SSR	paper.ex9g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * (X * _)); elpi z_report "paper.ex9g" "68" ltac_term:(G)) | idtac "SSR	paper.ex9g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + _ * (X * _)); elpi z_report "paper.ex9g" "69" ltac_term:(G)) | idtac "SSR	paper.ex9g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * (X * _) = _); elpi z_report "paper.ex9g" "70" ltac_term:(G)) | idtac "SSR	paper.ex9g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + _ * (X * _) = _); elpi z_report "paper.ex9g" "71" ltac_term:(G)) | idtac "SSR	paper.ex9g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _); elpi z_report "paper.ex9g" "72" ltac_term:(G)) | idtac "SSR	paper.ex9g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a + _ in X in X = _); elpi z_report "paper.ex9g" "73" ltac_term:(G)) | idtac "SSR	paper.ex9g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + _); elpi z_report "paper.ex9g" "74" ltac_term:(G)) | idtac "SSR	paper.ex9g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + b); elpi z_report "paper.ex9g" "75" ltac_term:(G)) | idtac "SSR	paper.ex9g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(a + _ in X in X = _); elpi z_report "paper.ex9g" "76" ltac_term:(G)) | idtac "SSR	paper.ex9g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (add); elpi z_report "paper.ex9g" "77" ltac_term:(G)) | idtac "SSR	paper.ex9g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex9g" "78" ltac_term:(G)) | idtac "SSR	paper.ex9g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(add); elpi z_report "paper.ex9g" "79" ltac_term:(G)) | idtac "SSR	paper.ex9g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (X + _) * _); elpi z_report "paper.ex9g" "80" ltac_term:(G)) | idtac "SSR	paper.ex9g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * ((X + _) * _)); elpi z_report "paper.ex9g" "81" ltac_term:(G)) | idtac "SSR	paper.ex9g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * ((X + _) * _)); elpi z_report "paper.ex9g" "82" ltac_term:(G)) | idtac "SSR	paper.ex9g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * ((X + _) * _) = _); elpi z_report "paper.ex9g" "83" ltac_term:(G)) | idtac "SSR	paper.ex9g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (a); elpi z_report "paper.ex9g" "84" ltac_term:(G)) | idtac "SSR	paper.ex9g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + b); elpi z_report "paper.ex9g" "85" ltac_term:(G)) | idtac "SSR	paper.ex9g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex9g" "86" ltac_term:(G)) | idtac "SSR	paper.ex9g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(a); elpi z_report "paper.ex9g" "87" ltac_term:(G)) | idtac "SSR	paper.ex9g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X + b); elpi z_report "paper.ex9g" "88" ltac_term:(G)) | idtac "SSR	paper.ex9g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (_ + X) * _); elpi z_report "paper.ex9g" "89" ltac_term:(G)) | idtac "SSR	paper.ex9g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * ((_ + X) * _)); elpi z_report "paper.ex9g" "90" ltac_term:(G)) | idtac "SSR	paper.ex9g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * ((_ + X) * _)); elpi z_report "paper.ex9g" "91" ltac_term:(G)) | idtac "SSR	paper.ex9g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * ((_ + X) * _) = _); elpi z_report "paper.ex9g" "92" ltac_term:(G)) | idtac "SSR	paper.ex9g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (b); elpi z_report "paper.ex9g" "93" ltac_term:(G)) | idtac "SSR	paper.ex9g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in a + X); elpi z_report "paper.ex9g" "94" ltac_term:(G)) | idtac "SSR	paper.ex9g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex9g" "95" ltac_term:(G)) | idtac "SSR	paper.ex9g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(b); elpi z_report "paper.ex9g" "96" ltac_term:(G)) | idtac "SSR	paper.ex9g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in a + X); elpi z_report "paper.ex9g" "97" ltac_term:(G)) | idtac "SSR	paper.ex9g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (d); elpi z_report "paper.ex9g" "98" ltac_term:(G)) | idtac "SSR	paper.ex9g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * (_ * X)); elpi z_report "paper.ex9g" "99" ltac_term:(G)) | idtac "SSR	paper.ex9g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * (_ * X)); elpi z_report "paper.ex9g" "100" ltac_term:(G)) | idtac "SSR	paper.ex9g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in (a + b) * X); elpi z_report "paper.ex9g" "101" ltac_term:(G)) | idtac "SSR	paper.ex9g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * (_ * X) = _); elpi z_report "paper.ex9g" "102" ltac_term:(G)) | idtac "SSR	paper.ex9g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(d); elpi z_report "paper.ex9g" "103" ltac_term:(G)) | idtac "SSR	paper.ex9g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "paper.ex9g" "104" ltac_term:(G)) | idtac "SSR	paper.ex9g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex9g" "105" ltac_term:(G)) | idtac "SSR	paper.ex9g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "paper.ex9g" "106" ltac_term:(G)) | idtac "SSR	paper.ex9g	106	error" ].
Abort.
End Ring.
End Paper.

(* Ex. 3: graph is defined with map; the pattern [graph _ n] matches graph,
   [map _ _] does not (keyed matching: map is not the head) *)
Definition graph (f : nat -> nat) n := map f (seq 0 n).
Goal forall (f g : nat -> nat) n, graph (fun x => f (g x)) n = graph g n.
intros f g n.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (graph _ n); elpi z_report "paper.ex3" "1" ltac_term:(G)) | idtac "SSR	paper.ex3	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (map _ _); elpi z_report "paper.ex3" "2" ltac_term:(G)) | idtac "SSR	paper.ex3	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (graph g _); elpi z_report "paper.ex3" "3" ltac_term:(G)) | idtac "SSR	paper.ex3	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex3g" "1" ltac_term:(G)) | idtac "SSR	paper.ex3g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(graph [x : nat in f (g x)] n = graph g n); elpi z_report "paper.ex3g" "2" ltac_term:(G)) | idtac "SSR	paper.ex3g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex3g" "3" ltac_term:(G)) | idtac "SSR	paper.ex3g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex3g" "4" ltac_term:(G)) | idtac "SSR	paper.ex3g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (list _); elpi z_report "paper.ex3g" "5" ltac_term:(G)) | idtac "SSR	paper.ex3g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(list nat); elpi z_report "paper.ex3g" "6" ltac_term:(G)) | idtac "SSR	paper.ex3g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (list); elpi z_report "paper.ex3g" "7" ltac_term:(G)) | idtac "SSR	paper.ex3g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(list); elpi z_report "paper.ex3g" "8" ltac_term:(G)) | idtac "SSR	paper.ex3g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in list X); elpi z_report "paper.ex3g" "9" ltac_term:(G)) | idtac "SSR	paper.ex3g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "paper.ex3g" "10" ltac_term:(G)) | idtac "SSR	paper.ex3g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "paper.ex3g" "11" ltac_term:(G)) | idtac "SSR	paper.ex3g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (graph _ _); elpi z_report "paper.ex3g" "12" ltac_term:(G)) | idtac "SSR	paper.ex3g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex3g" "13" ltac_term:(G)) | idtac "SSR	paper.ex3g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (graph _ _ as X in X = _); elpi z_report "paper.ex3g" "14" ltac_term:(G)) | idtac "SSR	paper.ex3g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(graph [x : nat in f (g x)] n); elpi z_report "paper.ex3g" "15" ltac_term:(G)) | idtac "SSR	paper.ex3g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(graph); elpi z_report "paper.ex3g" "16" ltac_term:(G)) | idtac "SSR	paper.ex3g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(graph); elpi z_report "paper.ex3g" "17" ltac_term:(G)) | idtac "SSR	paper.ex3g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in graph X _); elpi z_report "paper.ex3g" "18" ltac_term:(G)) | idtac "SSR	paper.ex3g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in graph X _ = _); elpi z_report "paper.ex3g" "19" ltac_term:(G)) | idtac "SSR	paper.ex3g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "paper.ex3g" "20" ltac_term:(G)) | idtac "SSR	paper.ex3g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "paper.ex3g" "21" ltac_term:(G)) | idtac "SSR	paper.ex3g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(nat); elpi z_report "paper.ex3g" "22" ltac_term:(G)) | idtac "SSR	paper.ex3g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (f); elpi z_report "paper.ex3g" "23" ltac_term:(G)) | idtac "SSR	paper.ex3g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(f); elpi z_report "paper.ex3g" "24" ltac_term:(G)) | idtac "SSR	paper.ex3g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g); elpi z_report "paper.ex3g" "25" ltac_term:(G)) | idtac "SSR	paper.ex3g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(g); elpi z_report "paper.ex3g" "26" ltac_term:(G)) | idtac "SSR	paper.ex3g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in graph _ X); elpi z_report "paper.ex3g" "27" ltac_term:(G)) | idtac "SSR	paper.ex3g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in graph _ X = _); elpi z_report "paper.ex3g" "28" ltac_term:(G)) | idtac "SSR	paper.ex3g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "paper.ex3g" "29" ltac_term:(G)) | idtac "SSR	paper.ex3g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "paper.ex3g" "30" ltac_term:(G)) | idtac "SSR	paper.ex3g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex3g" "31" ltac_term:(G)) | idtac "SSR	paper.ex3g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (graph g _); elpi z_report "paper.ex3g" "32" ltac_term:(G)) | idtac "SSR	paper.ex3g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (graph _ _ as X in _ = X); elpi z_report "paper.ex3g" "33" ltac_term:(G)) | idtac "SSR	paper.ex3g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(graph g n); elpi z_report "paper.ex3g" "34" ltac_term:(G)) | idtac "SSR	paper.ex3g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (graph); elpi z_report "paper.ex3g" "35" ltac_term:(G)) | idtac "SSR	paper.ex3g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(graph); elpi z_report "paper.ex3g" "36" ltac_term:(G)) | idtac "SSR	paper.ex3g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(graph); elpi z_report "paper.ex3g" "37" ltac_term:(G)) | idtac "SSR	paper.ex3g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = graph X _); elpi z_report "paper.ex3g" "38" ltac_term:(G)) | idtac "SSR	paper.ex3g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (g); elpi z_report "paper.ex3g" "39" ltac_term:(G)) | idtac "SSR	paper.ex3g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g); elpi z_report "paper.ex3g" "40" ltac_term:(G)) | idtac "SSR	paper.ex3g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(g); elpi z_report "paper.ex3g" "41" ltac_term:(G)) | idtac "SSR	paper.ex3g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in graph g X); elpi z_report "paper.ex3g" "42" ltac_term:(G)) | idtac "SSR	paper.ex3g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = graph _ X); elpi z_report "paper.ex3g" "43" ltac_term:(G)) | idtac "SSR	paper.ex3g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "paper.ex3g" "44" ltac_term:(G)) | idtac "SSR	paper.ex3g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "paper.ex3g" "45" ltac_term:(G)) | idtac "SSR	paper.ex3g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "paper.ex3g" "46" ltac_term:(G)) | idtac "SSR	paper.ex3g	46	error" ].
Abort.

(* Ex. 10: the first phase has no reduction: _ + (_ + _) is m + (m + n),
   not n + 2 * m (which is n + (m + (m + 0)) by computation) *)
Goal forall n m : nat, n + 2 * m = m + (m + n).
intros n m.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (_ + _)); elpi z_report "paper.ex10" "1" ltac_term:(G)) | idtac "SSR	paper.ex10	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n + _); elpi z_report "paper.ex10" "2" ltac_term:(G)) | idtac "SSR	paper.ex10	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (m + 0)); elpi z_report "paper.ex10" "3" ltac_term:(G)) | idtac "SSR	paper.ex10	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.ex10g" "1" ltac_term:(G)) | idtac "SSR	paper.ex10g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n + 2 * m = m + (m + n)); elpi z_report "paper.ex10g" "2" ltac_term:(G)) | idtac "SSR	paper.ex10g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.ex10g" "3" ltac_term:(G)) | idtac "SSR	paper.ex10g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.ex10g" "4" ltac_term:(G)) | idtac "SSR	paper.ex10g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "paper.ex10g" "5" ltac_term:(G)) | idtac "SSR	paper.ex10g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "paper.ex10g" "6" ltac_term:(G)) | idtac "SSR	paper.ex10g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.ex10g" "7" ltac_term:(G)) | idtac "SSR	paper.ex10g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.ex10g" "8" ltac_term:(G)) | idtac "SSR	paper.ex10g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.ex10g" "9" ltac_term:(G)) | idtac "SSR	paper.ex10g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n + 2 * m); elpi z_report "paper.ex10g" "10" ltac_term:(G)) | idtac "SSR	paper.ex10g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "paper.ex10g" "11" ltac_term:(G)) | idtac "SSR	paper.ex10g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "paper.ex10g" "12" ltac_term:(G)) | idtac "SSR	paper.ex10g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.ex10g" "13" ltac_term:(G)) | idtac "SSR	paper.ex10g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.ex10g" "14" ltac_term:(G)) | idtac "SSR	paper.ex10g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "paper.ex10g" "15" ltac_term:(G)) | idtac "SSR	paper.ex10g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(n); elpi z_report "paper.ex10g" "16" ltac_term:(G)) | idtac "SSR	paper.ex10g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _); elpi z_report "paper.ex10g" "17" ltac_term:(G)) | idtac "SSR	paper.ex10g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.ex10g" "18" ltac_term:(G)) | idtac "SSR	paper.ex10g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X); elpi z_report "paper.ex10g" "19" ltac_term:(G)) | idtac "SSR	paper.ex10g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ in X in X = _); elpi z_report "paper.ex10g" "20" ltac_term:(G)) | idtac "SSR	paper.ex10g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.ex10g" "21" ltac_term:(G)) | idtac "SSR	paper.ex10g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ * _ as X in _ + X = _); elpi z_report "paper.ex10g" "22" ltac_term:(G)) | idtac "SSR	paper.ex10g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2 * m); elpi z_report "paper.ex10g" "23" ltac_term:(G)) | idtac "SSR	paper.ex10g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.mul); elpi z_report "paper.ex10g" "24" ltac_term:(G)) | idtac "SSR	paper.ex10g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.mul); elpi z_report "paper.ex10g" "25" ltac_term:(G)) | idtac "SSR	paper.ex10g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "paper.ex10g" "26" ltac_term:(G)) | idtac "SSR	paper.ex10g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X * _); elpi z_report "paper.ex10g" "27" ltac_term:(G)) | idtac "SSR	paper.ex10g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X * _); elpi z_report "paper.ex10g" "28" ltac_term:(G)) | idtac "SSR	paper.ex10g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "paper.ex10g" "29" ltac_term:(G)) | idtac "SSR	paper.ex10g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X); elpi z_report "paper.ex10g" "30" ltac_term:(G)) | idtac "SSR	paper.ex10g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _); elpi z_report "paper.ex10g" "31" ltac_term:(G)) | idtac "SSR	paper.ex10g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X * _); elpi z_report "paper.ex10g" "32" ltac_term:(G)) | idtac "SSR	paper.ex10g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X = _); elpi z_report "paper.ex10g" "33" ltac_term:(G)) | idtac "SSR	paper.ex10g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X * _ = _); elpi z_report "paper.ex10g" "34" ltac_term:(G)) | idtac "SSR	paper.ex10g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + X * _ = _); elpi z_report "paper.ex10g" "35" ltac_term:(G)) | idtac "SSR	paper.ex10g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(2); elpi z_report "paper.ex10g" "36" ltac_term:(G)) | idtac "SSR	paper.ex10g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "paper.ex10g" "37" ltac_term:(G)) | idtac "SSR	paper.ex10g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "paper.ex10g" "38" ltac_term:(G)) | idtac "SSR	paper.ex10g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1); elpi z_report "paper.ex10g" "39" ltac_term:(G)) | idtac "SSR	paper.ex10g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "paper.ex10g" "40" ltac_term:(G)) | idtac "SSR	paper.ex10g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X); elpi z_report "paper.ex10g" "41" ltac_term:(G)) | idtac "SSR	paper.ex10g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X = _); elpi z_report "paper.ex10g" "42" ltac_term:(G)) | idtac "SSR	paper.ex10g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X); elpi z_report "paper.ex10g" "43" ltac_term:(G)) | idtac "SSR	paper.ex10g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in X * _); elpi z_report "paper.ex10g" "44" ltac_term:(G)) | idtac "SSR	paper.ex10g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X * _); elpi z_report "paper.ex10g" "45" ltac_term:(G)) | idtac "SSR	paper.ex10g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in S X * _); elpi z_report "paper.ex10g" "46" ltac_term:(G)) | idtac "SSR	paper.ex10g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X = _); elpi z_report "paper.ex10g" "47" ltac_term:(G)) | idtac "SSR	paper.ex10g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 in X in _ + X * _); elpi z_report "paper.ex10g" "48" ltac_term:(G)) | idtac "SSR	paper.ex10g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X * _); elpi z_report "paper.ex10g" "49" ltac_term:(G)) | idtac "SSR	paper.ex10g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + S X * _); elpi z_report "paper.ex10g" "50" ltac_term:(G)) | idtac "SSR	paper.ex10g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S X * _ = _); elpi z_report "paper.ex10g" "51" ltac_term:(G)) | idtac "SSR	paper.ex10g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + S X * _ = _); elpi z_report "paper.ex10g" "52" ltac_term:(G)) | idtac "SSR	paper.ex10g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "paper.ex10g" "53" ltac_term:(G)) | idtac "SSR	paper.ex10g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "paper.ex10g" "54" ltac_term:(G)) | idtac "SSR	paper.ex10g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "paper.ex10g" "55" ltac_term:(G)) | idtac "SSR	paper.ex10g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "paper.ex10g" "56" ltac_term:(G)) | idtac "SSR	paper.ex10g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "paper.ex10g" "57" ltac_term:(G)) | idtac "SSR	paper.ex10g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X)); elpi z_report "paper.ex10g" "58" ltac_term:(G)) | idtac "SSR	paper.ex10g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S (S X) * _); elpi z_report "paper.ex10g" "59" ltac_term:(G)) | idtac "SSR	paper.ex10g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S (S X) * _); elpi z_report "paper.ex10g" "60" ltac_term:(G)) | idtac "SSR	paper.ex10g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + S (S X) * _ = _); elpi z_report "paper.ex10g" "61" ltac_term:(G)) | idtac "SSR	paper.ex10g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "paper.ex10g" "62" ltac_term:(G)) | idtac "SSR	paper.ex10g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ * X); elpi z_report "paper.ex10g" "63" ltac_term:(G)) | idtac "SSR	paper.ex10g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X); elpi z_report "paper.ex10g" "64" ltac_term:(G)) | idtac "SSR	paper.ex10g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + _ * X = _); elpi z_report "paper.ex10g" "65" ltac_term:(G)) | idtac "SSR	paper.ex10g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "paper.ex10g" "66" ltac_term:(G)) | idtac "SSR	paper.ex10g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "paper.ex10g" "67" ltac_term:(G)) | idtac "SSR	paper.ex10g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.ex10g" "68" ltac_term:(G)) | idtac "SSR	paper.ex10g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (m + _); elpi z_report "paper.ex10g" "69" ltac_term:(G)) | idtac "SSR	paper.ex10g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = X); elpi z_report "paper.ex10g" "70" ltac_term:(G)) | idtac "SSR	paper.ex10g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m + (m + n)); elpi z_report "paper.ex10g" "71" ltac_term:(G)) | idtac "SSR	paper.ex10g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "paper.ex10g" "72" ltac_term:(G)) | idtac "SSR	paper.ex10g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "paper.ex10g" "73" ltac_term:(G)) | idtac "SSR	paper.ex10g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X + _); elpi z_report "paper.ex10g" "74" ltac_term:(G)) | idtac "SSR	paper.ex10g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (m + n)); elpi z_report "paper.ex10g" "75" ltac_term:(G)) | idtac "SSR	paper.ex10g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "paper.ex10g" "76" ltac_term:(G)) | idtac "SSR	paper.ex10g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "paper.ex10g" "77" ltac_term:(G)) | idtac "SSR	paper.ex10g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n); elpi z_report "paper.ex10g" "78" ltac_term:(G)) | idtac "SSR	paper.ex10g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in m + X); elpi z_report "paper.ex10g" "79" ltac_term:(G)) | idtac "SSR	paper.ex10g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "paper.ex10g" "80" ltac_term:(G)) | idtac "SSR	paper.ex10g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + X); elpi z_report "paper.ex10g" "81" ltac_term:(G)) | idtac "SSR	paper.ex10g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + n in X in _ = X); elpi z_report "paper.ex10g" "82" ltac_term:(G)) | idtac "SSR	paper.ex10g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ = _ + X); elpi z_report "paper.ex10g" "83" ltac_term:(G)) | idtac "SSR	paper.ex10g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m + n); elpi z_report "paper.ex10g" "84" ltac_term:(G)) | idtac "SSR	paper.ex10g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "paper.ex10g" "85" ltac_term:(G)) | idtac "SSR	paper.ex10g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "paper.ex10g" "86" ltac_term:(G)) | idtac "SSR	paper.ex10g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "paper.ex10g" "87" ltac_term:(G)) | idtac "SSR	paper.ex10g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + n); elpi z_report "paper.ex10g" "88" ltac_term:(G)) | idtac "SSR	paper.ex10g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "paper.ex10g" "89" ltac_term:(G)) | idtac "SSR	paper.ex10g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (X + _)); elpi z_report "paper.ex10g" "90" ltac_term:(G)) | idtac "SSR	paper.ex10g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (m); elpi z_report "paper.ex10g" "91" ltac_term:(G)) | idtac "SSR	paper.ex10g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "paper.ex10g" "92" ltac_term:(G)) | idtac "SSR	paper.ex10g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "paper.ex10g" "93" ltac_term:(G)) | idtac "SSR	paper.ex10g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "paper.ex10g" "94" ltac_term:(G)) | idtac "SSR	paper.ex10g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = _ + (_ + X)); elpi z_report "paper.ex10g" "95" ltac_term:(G)) | idtac "SSR	paper.ex10g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (n); elpi z_report "paper.ex10g" "96" ltac_term:(G)) | idtac "SSR	paper.ex10g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "paper.ex10g" "97" ltac_term:(G)) | idtac "SSR	paper.ex10g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(n); elpi z_report "paper.ex10g" "98" ltac_term:(G)) | idtac "SSR	paper.ex10g	98	error" ].
Abort.

(* section 3.2: the occurrences of 1 + m are compared argument by argument:
   1 + (0 + m) is one, 0 + (1 + m) is not *)
Goal forall m : nat, (1 + m) + (1 + (0 + m)) + (0 + (1 + m)) = 0.
intros m.
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + _); elpi z_report "paper.s32" "1" ltac_term:(G)) | idtac "SSR	paper.s32	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m); elpi z_report "paper.s32" "2" ltac_term:(G)) | idtac "SSR	paper.s32	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ = _); elpi z_report "paper.s32g" "1" ltac_term:(G)) | idtac "SSR	paper.s32g	1	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + m + (1 + (0 + m)) + (0 + (1 + m)) = 0); elpi z_report "paper.s32g" "2" ltac_term:(G)) | idtac "SSR	paper.s32g	2	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (@eq); elpi z_report "paper.s32g" "3" ltac_term:(G)) | idtac "SSR	paper.s32g	3	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(@eq); elpi z_report "paper.s32g" "4" ltac_term:(G)) | idtac "SSR	paper.s32g	4	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (nat); elpi z_report "paper.s32g" "5" ltac_term:(G)) | idtac "SSR	paper.s32g	5	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(nat); elpi z_report "paper.s32g" "6" ltac_term:(G)) | idtac "SSR	paper.s32g	6	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _); elpi z_report "paper.s32g" "7" ltac_term:(G)) | idtac "SSR	paper.s32g	7	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X = _); elpi z_report "paper.s32g" "8" ltac_term:(G)) | idtac "SSR	paper.s32g	8	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X = _); elpi z_report "paper.s32g" "9" ltac_term:(G)) | idtac "SSR	paper.s32g	9	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + m + (1 + (0 + m)) + (0 + (1 + m))); elpi z_report "paper.s32g" "10" ltac_term:(G)) | idtac "SSR	paper.s32g	10	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "paper.s32g" "11" ltac_term:(G)) | idtac "SSR	paper.s32g	11	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(Nat.add); elpi z_report "paper.s32g" "12" ltac_term:(G)) | idtac "SSR	paper.s32g	12	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _); elpi z_report "paper.s32g" "13" ltac_term:(G)) | idtac "SSR	paper.s32g	13	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _); elpi z_report "paper.s32g" "14" ltac_term:(G)) | idtac "SSR	paper.s32g	14	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ = _); elpi z_report "paper.s32g" "15" ltac_term:(G)) | idtac "SSR	paper.s32g	15	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m + _); elpi z_report "paper.s32g" "16" ltac_term:(G)) | idtac "SSR	paper.s32g	16	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ = _); elpi z_report "paper.s32g" "17" ltac_term:(G)) | idtac "SSR	paper.s32g	17	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m + _ in X in X = _); elpi z_report "paper.s32g" "18" ltac_term:(G)) | idtac "SSR	paper.s32g	18	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + m + (1 + (0 + m))); elpi z_report "paper.s32g" "19" ltac_term:(G)) | idtac "SSR	paper.s32g	19	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "paper.s32g" "20" ltac_term:(G)) | idtac "SSR	paper.s32g	20	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(Nat.add); elpi z_report "paper.s32g" "21" ltac_term:(G)) | idtac "SSR	paper.s32g	21	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _); elpi z_report "paper.s32g" "22" ltac_term:(G)) | idtac "SSR	paper.s32g	22	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (1 + _)); elpi z_report "paper.s32g" "23" ltac_term:(G)) | idtac "SSR	paper.s32g	23	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m as X in X + _); elpi z_report "paper.s32g" "24" ltac_term:(G)) | idtac "SSR	paper.s32g	24	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ + _); elpi z_report "paper.s32g" "25" ltac_term:(G)) | idtac "SSR	paper.s32g	25	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ = _); elpi z_report "paper.s32g" "26" ltac_term:(G)) | idtac "SSR	paper.s32g	26	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in X + _ + _ = _); elpi z_report "paper.s32g" "27" ltac_term:(G)) | idtac "SSR	paper.s32g	27	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m); elpi z_report "paper.s32g" "28" ltac_term:(G)) | idtac "SSR	paper.s32g	28	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m in X in X = _); elpi z_report "paper.s32g" "29" ltac_term:(G)) | idtac "SSR	paper.s32g	29	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m in X in X + _); elpi z_report "paper.s32g" "30" ltac_term:(G)) | idtac "SSR	paper.s32g	30	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m in X in X + _ = _); elpi z_report "paper.s32g" "31" ltac_term:(G)) | idtac "SSR	paper.s32g	31	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + m); elpi z_report "paper.s32g" "32" ltac_term:(G)) | idtac "SSR	paper.s32g	32	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1 + m); elpi z_report "paper.s32g" "33" ltac_term:(G)) | idtac "SSR	paper.s32g	33	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + m in X in X = _); elpi z_report "paper.s32g" "34" ltac_term:(G)) | idtac "SSR	paper.s32g	34	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + m in X in X + _); elpi z_report "paper.s32g" "35" ltac_term:(G)) | idtac "SSR	paper.s32g	35	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(_ + m in X in X + _ = _); elpi z_report "paper.s32g" "36" ltac_term:(G)) | idtac "SSR	paper.s32g	36	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "paper.s32g" "37" ltac_term:(G)) | idtac "SSR	paper.s32g	37	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(Nat.add); elpi z_report "paper.s32g" "38" ltac_term:(G)) | idtac "SSR	paper.s32g	38	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + m + _); elpi z_report "paper.s32g" "39" ltac_term:(G)) | idtac "SSR	paper.s32g	39	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ + _); elpi z_report "paper.s32g" "40" ltac_term:(G)) | idtac "SSR	paper.s32g	40	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + _ + _); elpi z_report "paper.s32g" "41" ltac_term:(G)) | idtac "SSR	paper.s32g	41	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ + _); elpi z_report "paper.s32g" "42" ltac_term:(G)) | idtac "SSR	paper.s32g	42	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + (1 + _)); elpi z_report "paper.s32g" "43" ltac_term:(G)) | idtac "SSR	paper.s32g	43	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ + _ + _); elpi z_report "paper.s32g" "44" ltac_term:(G)) | idtac "SSR	paper.s32g	44	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + _ + _ + _ = _); elpi z_report "paper.s32g" "45" ltac_term:(G)) | idtac "SSR	paper.s32g	45	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _ + _ + _ = _); elpi z_report "paper.s32g" "46" ltac_term:(G)) | idtac "SSR	paper.s32g	46	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + m); elpi z_report "paper.s32g" "47" ltac_term:(G)) | idtac "SSR	paper.s32g	47	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + _); elpi z_report "paper.s32g" "48" ltac_term:(G)) | idtac "SSR	paper.s32g	48	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(1); elpi z_report "paper.s32g" "49" ltac_term:(G)) | idtac "SSR	paper.s32g	49	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _); elpi z_report "paper.s32g" "50" ltac_term:(G)) | idtac "SSR	paper.s32g	50	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in X + m); elpi z_report "paper.s32g" "51" ltac_term:(G)) | idtac "SSR	paper.s32g	51	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ as X in X + _); elpi z_report "paper.s32g" "52" ltac_term:(G)) | idtac "SSR	paper.s32g	52	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X = _); elpi z_report "paper.s32g" "53" ltac_term:(G)) | idtac "SSR	paper.s32g	53	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X + _); elpi z_report "paper.s32g" "54" ltac_term:(G)) | idtac "SSR	paper.s32g	54	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S _ in X in X + _ = _); elpi z_report "paper.s32g" "55" ltac_term:(G)) | idtac "SSR	paper.s32g	55	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "paper.s32g" "56" ltac_term:(G)) | idtac "SSR	paper.s32g	56	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(S); elpi z_report "paper.s32g" "57" ltac_term:(G)) | idtac "SSR	paper.s32g	57	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ + _); elpi z_report "paper.s32g" "58" ltac_term:(G)) | idtac "SSR	paper.s32g	58	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ + _ + _); elpi z_report "paper.s32g" "59" ltac_term:(G)) | idtac "SSR	paper.s32g	59	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _ + _ + _ = _); elpi z_report "paper.s32g" "60" ltac_term:(G)) | idtac "SSR	paper.s32g	60	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + _); elpi z_report "paper.s32g" "61" ltac_term:(G)) | idtac "SSR	paper.s32g	61	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "paper.s32g" "62" ltac_term:(G)) | idtac "SSR	paper.s32g	62	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0); elpi z_report "paper.s32g" "63" ltac_term:(G)) | idtac "SSR	paper.s32g	63	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X); elpi z_report "paper.s32g" "64" ltac_term:(G)) | idtac "SSR	paper.s32g	64	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in S X + _); elpi z_report "paper.s32g" "65" ltac_term:(G)) | idtac "SSR	paper.s32g	65	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + X + _); elpi z_report "paper.s32g" "66" ltac_term:(G)) | idtac "SSR	paper.s32g	66	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ + _); elpi z_report "paper.s32g" "67" ltac_term:(G)) | idtac "SSR	paper.s32g	67	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ + _ = _); elpi z_report "paper.s32g" "68" ltac_term:(G)) | idtac "SSR	paper.s32g	68	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + X); elpi z_report "paper.s32g" "69" ltac_term:(G)) | idtac "SSR	paper.s32g	69	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "paper.s32g" "70" ltac_term:(G)) | idtac "SSR	paper.s32g	70	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(m); elpi z_report "paper.s32g" "71" ltac_term:(G)) | idtac "SSR	paper.s32g	71	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(X in 1 + X); elpi z_report "paper.s32g" "72" ltac_term:(G)) | idtac "SSR	paper.s32g	72	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _); elpi z_report "paper.s32g" "73" ltac_term:(G)) | idtac "SSR	paper.s32g	73	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + m + X); elpi z_report "paper.s32g" "74" ltac_term:(G)) | idtac "SSR	paper.s32g	74	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _); elpi z_report "paper.s32g" "75" ltac_term:(G)) | idtac "SSR	paper.s32g	75	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X + _ = _); elpi z_report "paper.s32g" "76" ltac_term:(G)) | idtac "SSR	paper.s32g	76	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + m + X); elpi z_report "paper.s32g" "77" ltac_term:(G)) | idtac "SSR	paper.s32g	77	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X + _ = _); elpi z_report "paper.s32g" "78" ltac_term:(G)) | idtac "SSR	paper.s32g	78	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (_ + m)); elpi z_report "paper.s32g" "79" ltac_term:(G)) | idtac "SSR	paper.s32g	79	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (_ + m) in X in X = _); elpi z_report "paper.s32g" "80" ltac_term:(G)) | idtac "SSR	paper.s32g	80	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (0 + _) in X in X + _); elpi z_report "paper.s32g" "81" ltac_term:(G)) | idtac "SSR	paper.s32g	81	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + (0 + _) in X in X + _ = _); elpi z_report "paper.s32g" "82" ltac_term:(G)) | idtac "SSR	paper.s32g	82	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + (_ + m)); elpi z_report "paper.s32g" "83" ltac_term:(G)) | idtac "SSR	paper.s32g	83	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + (_ + m) in X in X = _); elpi z_report "paper.s32g" "84" ltac_term:(G)) | idtac "SSR	paper.s32g	84	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + (0 + _) in X in X + _); elpi z_report "paper.s32g" "85" ltac_term:(G)) | idtac "SSR	paper.s32g	85	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1 + (0 + m)); elpi z_report "paper.s32g" "86" ltac_term:(G)) | idtac "SSR	paper.s32g	86	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + (0 + _) in X in X + _ = _); elpi z_report "paper.s32g" "87" ltac_term:(G)) | idtac "SSR	paper.s32g	87	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "paper.s32g" "88" ltac_term:(G)) | idtac "SSR	paper.s32g	88	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(Nat.add); elpi z_report "paper.s32g" "89" ltac_term:(G)) | idtac "SSR	paper.s32g	89	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X + _); elpi z_report "paper.s32g" "90" ltac_term:(G)) | idtac "SSR	paper.s32g	90	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + (X + _)); elpi z_report "paper.s32g" "91" ltac_term:(G)) | idtac "SSR	paper.s32g	91	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _); elpi z_report "paper.s32g" "92" ltac_term:(G)) | idtac "SSR	paper.s32g	92	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + m + X); elpi z_report "paper.s32g" "93" ltac_term:(G)) | idtac "SSR	paper.s32g	93	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + m + (X + _)); elpi z_report "paper.s32g" "94" ltac_term:(G)) | idtac "SSR	paper.s32g	94	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + (X + _) + _); elpi z_report "paper.s32g" "95" ltac_term:(G)) | idtac "SSR	paper.s32g	95	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) + _ = _); elpi z_report "paper.s32g" "96" ltac_term:(G)) | idtac "SSR	paper.s32g	96	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + (X + _) + _ = _); elpi z_report "paper.s32g" "97" ltac_term:(G)) | idtac "SSR	paper.s32g	97	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + _); elpi z_report "paper.s32g" "98" ltac_term:(G)) | idtac "SSR	paper.s32g	98	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (_ + m)); elpi z_report "paper.s32g" "99" ltac_term:(G)) | idtac "SSR	paper.s32g	99	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X + _ = _); elpi z_report "paper.s32g" "100" ltac_term:(G)) | idtac "SSR	paper.s32g	100	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + (0 + m)); elpi z_report "paper.s32g" "101" ltac_term:(G)) | idtac "SSR	paper.s32g	101	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(1); elpi z_report "paper.s32g" "102" ltac_term:(G)) | idtac "SSR	paper.s32g	102	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _); elpi z_report "paper.s32g" "103" ltac_term:(G)) | idtac "SSR	paper.s32g	103	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X = _); elpi z_report "paper.s32g" "104" ltac_term:(G)) | idtac "SSR	paper.s32g	104	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X + _); elpi z_report "paper.s32g" "105" ltac_term:(G)) | idtac "SSR	paper.s32g	105	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in X + (_ + m)); elpi z_report "paper.s32g" "106" ltac_term:(G)) | idtac "SSR	paper.s32g	106	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ in X in X + _ = _); elpi z_report "paper.s32g" "107" ltac_term:(G)) | idtac "SSR	paper.s32g	107	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S _ as X in X + (0 + m)); elpi z_report "paper.s32g" "108" ltac_term:(G)) | idtac "SSR	paper.s32g	108	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "paper.s32g" "109" ltac_term:(G)) | idtac "SSR	paper.s32g	109	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(S); elpi z_report "paper.s32g" "110" ltac_term:(G)) | idtac "SSR	paper.s32g	110	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (S X + _)); elpi z_report "paper.s32g" "111" ltac_term:(G)) | idtac "SSR	paper.s32g	111	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (S X + _) + _); elpi z_report "paper.s32g" "112" ltac_term:(G)) | idtac "SSR	paper.s32g	112	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (S X + _) + _ = _); elpi z_report "paper.s32g" "113" ltac_term:(G)) | idtac "SSR	paper.s32g	113	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + (0 + m)); elpi z_report "paper.s32g" "114" ltac_term:(G)) | idtac "SSR	paper.s32g	114	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "paper.s32g" "115" ltac_term:(G)) | idtac "SSR	paper.s32g	115	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(0); elpi z_report "paper.s32g" "116" ltac_term:(G)) | idtac "SSR	paper.s32g	116	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X); elpi z_report "paper.s32g" "117" ltac_term:(G)) | idtac "SSR	paper.s32g	117	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in S X + (0 + m)); elpi z_report "paper.s32g" "118" ltac_term:(G)) | idtac "SSR	paper.s32g	118	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _); elpi z_report "paper.s32g" "119" ltac_term:(G)) | idtac "SSR	paper.s32g	119	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _ in X in X = _); elpi z_report "paper.s32g" "120" ltac_term:(G)) | idtac "SSR	paper.s32g	120	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _ in X in X + _); elpi z_report "paper.s32g" "121" ltac_term:(G)) | idtac "SSR	paper.s32g	121	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _); elpi z_report "paper.s32g" "122" ltac_term:(G)) | idtac "SSR	paper.s32g	122	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + m + (_ + X)); elpi z_report "paper.s32g" "123" ltac_term:(G)) | idtac "SSR	paper.s32g	123	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _ in X in X + _ = _); elpi z_report "paper.s32g" "124" ltac_term:(G)) | idtac "SSR	paper.s32g	124	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _ in X in _ + X + _); elpi z_report "paper.s32g" "125" ltac_term:(G)) | idtac "SSR	paper.s32g	125	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _ as X in _ + (_ + X)); elpi z_report "paper.s32g" "126" ltac_term:(G)) | idtac "SSR	paper.s32g	126	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + (_ + X) + _); elpi z_report "paper.s32g" "127" ltac_term:(G)) | idtac "SSR	paper.s32g	127	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) + _ = _); elpi z_report "paper.s32g" "128" ltac_term:(G)) | idtac "SSR	paper.s32g	128	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + _ in X in _ + m + X); elpi z_report "paper.s32g" "129" ltac_term:(G)) | idtac "SSR	paper.s32g	129	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + (_ + X) + _ = _); elpi z_report "paper.s32g" "130" ltac_term:(G)) | idtac "SSR	paper.s32g	130	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m as X in _ + X); elpi z_report "paper.s32g" "131" ltac_term:(G)) | idtac "SSR	paper.s32g	131	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 + m); elpi z_report "paper.s32g" "132" ltac_term:(G)) | idtac "SSR	paper.s32g	132	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(_ + m as X in _ + X); elpi z_report "paper.s32g" "133" ltac_term:(G)) | idtac "SSR	paper.s32g	133	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Nat.add); elpi z_report "paper.s32g" "134" ltac_term:(G)) | idtac "SSR	paper.s32g	134	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(Nat.add); elpi z_report "paper.s32g" "135" ltac_term:(G)) | idtac "SSR	paper.s32g	135	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (X + _)) + _); elpi z_report "paper.s32g" "136" ltac_term:(G)) | idtac "SSR	paper.s32g	136	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + m + (_ + (X + _))); elpi z_report "paper.s32g" "137" ltac_term:(G)) | idtac "SSR	paper.s32g	137	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (X + _)) + _ = _); elpi z_report "paper.s32g" "138" ltac_term:(G)) | idtac "SSR	paper.s32g	138	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + m)); elpi z_report "paper.s32g" "139" ltac_term:(G)) | idtac "SSR	paper.s32g	139	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "paper.s32g" "140" ltac_term:(G)) | idtac "SSR	paper.s32g	140	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(0); elpi z_report "paper.s32g" "141" ltac_term:(G)) | idtac "SSR	paper.s32g	141	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in _ + (X + m)); elpi z_report "paper.s32g" "142" ltac_term:(G)) | idtac "SSR	paper.s32g	142	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + X); elpi z_report "paper.s32g" "143" ltac_term:(G)) | idtac "SSR	paper.s32g	143	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (0 + X))); elpi z_report "paper.s32g" "144" ltac_term:(G)) | idtac "SSR	paper.s32g	144	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (_ + X)) + _); elpi z_report "paper.s32g" "145" ltac_term:(G)) | idtac "SSR	paper.s32g	145	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (_ + X)) + _ = _); elpi z_report "paper.s32g" "146" ltac_term:(G)) | idtac "SSR	paper.s32g	146	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 1 + (_ + X)); elpi z_report "paper.s32g" "147" ltac_term:(G)) | idtac "SSR	paper.s32g	147	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "paper.s32g" "148" ltac_term:(G)) | idtac "SSR	paper.s32g	148	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(m); elpi z_report "paper.s32g" "149" ltac_term:(G)) | idtac "SSR	paper.s32g	149	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {2}(X in 1 + (_ + X)); elpi z_report "paper.s32g" "150" ltac_term:(G)) | idtac "SSR	paper.s32g	150	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X); elpi z_report "paper.s32g" "151" ltac_term:(G)) | idtac "SSR	paper.s32g	151	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X); elpi z_report "paper.s32g" "152" ltac_term:(G)) | idtac "SSR	paper.s32g	152	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + X = _); elpi z_report "paper.s32g" "153" ltac_term:(G)) | idtac "SSR	paper.s32g	153	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + X = _); elpi z_report "paper.s32g" "154" ltac_term:(G)) | idtac "SSR	paper.s32g	154	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + (_ + m)); elpi z_report "paper.s32g" "155" ltac_term:(G)) | idtac "SSR	paper.s32g	155	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0 + (_ + m) in X in X = _); elpi z_report "paper.s32g" "156" ltac_term:(G)) | idtac "SSR	paper.s32g	156	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {1}(0 + (1 + m)); elpi z_report "paper.s32g" "157" ltac_term:(G)) | idtac "SSR	paper.s32g	157	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(Nat.add); elpi z_report "paper.s32g" "158" ltac_term:(G)) | idtac "SSR	paper.s32g	158	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(Nat.add); elpi z_report "paper.s32g" "159" ltac_term:(G)) | idtac "SSR	paper.s32g	159	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _)); elpi z_report "paper.s32g" "160" ltac_term:(G)) | idtac "SSR	paper.s32g	160	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (X + _) = _); elpi z_report "paper.s32g" "161" ltac_term:(G)) | idtac "SSR	paper.s32g	161	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in X + (1 + m)); elpi z_report "paper.s32g" "162" ltac_term:(G)) | idtac "SSR	paper.s32g	162	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(0); elpi z_report "paper.s32g" "163" ltac_term:(G)) | idtac "SSR	paper.s32g	163	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {4}(0); elpi z_report "paper.s32g" "164" ltac_term:(G)) | idtac "SSR	paper.s32g	164	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X)); elpi z_report "paper.s32g" "165" ltac_term:(G)) | idtac "SSR	paper.s32g	165	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in 0 + X); elpi z_report "paper.s32g" "166" ltac_term:(G)) | idtac "SSR	paper.s32g	166	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m in X in _ + X); elpi z_report "paper.s32g" "167" ltac_term:(G)) | idtac "SSR	paper.s32g	167	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + (_ + X)); elpi z_report "paper.s32g" "168" ltac_term:(G)) | idtac "SSR	paper.s32g	168	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + X) = _); elpi z_report "paper.s32g" "169" ltac_term:(G)) | idtac "SSR	paper.s32g	169	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + m in X in _ + X = _); elpi z_report "paper.s32g" "170" ltac_term:(G)) | idtac "SSR	paper.s32g	170	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (_ + _ as X in _ + (_ + X) = _); elpi z_report "paper.s32g" "171" ltac_term:(G)) | idtac "SSR	paper.s32g	171	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + m); elpi z_report "paper.s32g" "172" ltac_term:(G)) | idtac "SSR	paper.s32g	172	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (1 + m in X in X = _); elpi z_report "paper.s32g" "173" ltac_term:(G)) | idtac "SSR	paper.s32g	173	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 + m); elpi z_report "paper.s32g" "174" ltac_term:(G)) | idtac "SSR	paper.s32g	174	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 + m); elpi z_report "paper.s32g" "175" ltac_term:(G)) | idtac "SSR	paper.s32g	175	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1 + m in X in X = _); elpi z_report "paper.s32g" "176" ltac_term:(G)) | idtac "SSR	paper.s32g	176	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (Nat.add); elpi z_report "paper.s32g" "177" ltac_term:(G)) | idtac "SSR	paper.s32g	177	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(Nat.add); elpi z_report "paper.s32g" "178" ltac_term:(G)) | idtac "SSR	paper.s32g	178	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {7}(Nat.add); elpi z_report "paper.s32g" "179" ltac_term:(G)) | idtac "SSR	paper.s32g	179	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X); elpi z_report "paper.s32g" "180" ltac_term:(G)) | idtac "SSR	paper.s32g	180	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + (X + _)); elpi z_report "paper.s32g" "181" ltac_term:(G)) | idtac "SSR	paper.s32g	181	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + X = _); elpi z_report "paper.s32g" "182" ltac_term:(G)) | idtac "SSR	paper.s32g	182	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in _ + (_ + X)); elpi z_report "paper.s32g" "183" ltac_term:(G)) | idtac "SSR	paper.s32g	183	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (X + _))); elpi z_report "paper.s32g" "184" ltac_term:(G)) | idtac "SSR	paper.s32g	184	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in 0 + (X + _)); elpi z_report "paper.s32g" "185" ltac_term:(G)) | idtac "SSR	paper.s32g	185	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + (_ + (X + _))); elpi z_report "paper.s32g" "186" ltac_term:(G)) | idtac "SSR	paper.s32g	186	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (X + _)) = _); elpi z_report "paper.s32g" "187" ltac_term:(G)) | idtac "SSR	paper.s32g	187	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in _ + (_ + (X + _)) = _); elpi z_report "paper.s32g" "188" ltac_term:(G)) | idtac "SSR	paper.s32g	188	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _); elpi z_report "paper.s32g" "189" ltac_term:(G)) | idtac "SSR	paper.s32g	189	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ in X in X = _); elpi z_report "paper.s32g" "190" ltac_term:(G)) | idtac "SSR	paper.s32g	190	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S _ as X in X + m); elpi z_report "paper.s32g" "191" ltac_term:(G)) | idtac "SSR	paper.s32g	191	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(1); elpi z_report "paper.s32g" "192" ltac_term:(G)) | idtac "SSR	paper.s32g	192	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _); elpi z_report "paper.s32g" "193" ltac_term:(G)) | idtac "SSR	paper.s32g	193	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ in X in X = _); elpi z_report "paper.s32g" "194" ltac_term:(G)) | idtac "SSR	paper.s32g	194	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S _ as X in X + m); elpi z_report "paper.s32g" "195" ltac_term:(G)) | idtac "SSR	paper.s32g	195	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (S); elpi z_report "paper.s32g" "196" ltac_term:(G)) | idtac "SSR	paper.s32g	196	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "paper.s32g" "197" ltac_term:(G)) | idtac "SSR	paper.s32g	197	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(S); elpi z_report "paper.s32g" "198" ltac_term:(G)) | idtac "SSR	paper.s32g	198	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + (S X + _)); elpi z_report "paper.s32g" "199" ltac_term:(G)) | idtac "SSR	paper.s32g	199	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (S X + _))); elpi z_report "paper.s32g" "200" ltac_term:(G)) | idtac "SSR	paper.s32g	200	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (S X + _)) = _); elpi z_report "paper.s32g" "201" ltac_term:(G)) | idtac "SSR	paper.s32g	201	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X); elpi z_report "paper.s32g" "202" ltac_term:(G)) | idtac "SSR	paper.s32g	202	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in S X + m); elpi z_report "paper.s32g" "203" ltac_term:(G)) | idtac "SSR	paper.s32g	203	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(0); elpi z_report "paper.s32g" "204" ltac_term:(G)) | idtac "SSR	paper.s32g	204	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {5}(0); elpi z_report "paper.s32g" "205" ltac_term:(G)) | idtac "SSR	paper.s32g	205	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S X); elpi z_report "paper.s32g" "206" ltac_term:(G)) | idtac "SSR	paper.s32g	206	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(X in S X + m); elpi z_report "paper.s32g" "207" ltac_term:(G)) | idtac "SSR	paper.s32g	207	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in 0 + (_ + X)); elpi z_report "paper.s32g" "208" ltac_term:(G)) | idtac "SSR	paper.s32g	208	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (_ + X))); elpi z_report "paper.s32g" "209" ltac_term:(G)) | idtac "SSR	paper.s32g	209	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ + (_ + (_ + X)) = _); elpi z_report "paper.s32g" "210" ltac_term:(G)) | idtac "SSR	paper.s32g	210	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (m); elpi z_report "paper.s32g" "211" ltac_term:(G)) | idtac "SSR	paper.s32g	211	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "paper.s32g" "212" ltac_term:(G)) | idtac "SSR	paper.s32g	212	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {3}(m); elpi z_report "paper.s32g" "213" ltac_term:(G)) | idtac "SSR	paper.s32g	213	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (X in _ = X); elpi z_report "paper.s32g" "214" ltac_term:(G)) | idtac "SSR	paper.s32g	214	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := (0); elpi z_report "paper.s32g" "215" ltac_term:(G)) | idtac "SSR	paper.s32g	215	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(0); elpi z_report "paper.s32g" "216" ltac_term:(G)) | idtac "SSR	paper.s32g	216	error" ].
let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := {6}(0); elpi z_report "paper.s32g" "217" ltac_term:(G)) | idtac "SSR	paper.s32g	217	error" ].
Abort.
