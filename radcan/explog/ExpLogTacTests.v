(******************************************************************************)
(* Tests of explog (ExpLogTac.v): all the goals of the earlier test files     *)
(* (proto/ExpLogTests0.v, ExpLogExpTests.v, ExpLogLnTests.v, ExpLogHypTests.v, *)
(* ExpLogTrigTests.v, and the tests of the generic pieces ExpLogGExpTests.v,  *)
(* ExpLogGLnTests.v), deduplicated, grouped by topic.                         *)
(*                                                                            *)
(* A goal that holds under conditions is proved as a Lemma with the conditions *)
(* as hypotheses (explog closes them from the context); the same goal without *)
(* hypotheses is then run as a Goal that checks the conditions explog gives   *)
(* back (left_is, in order), and aborted.                                     *)
(*                                                                            *)
(* Summary:                                                                   *)
(*   proved, no condition         42                                          *)
(*   proved, conditions given back 39                                         *)
(*   needing a heuristic          H1: 3, H3: 3, H5: 2 (H2, H4 always run)     *)
(*   must fail, failing           9                                           *)
(*   unexpected failures          0                                           *)
(*   every explog call takes less than 1 s                                    *)
(*                                                                            *)
(* Table: goal / conditions given back without hypotheses / core (generic     *)
(* procedure, with the condition clean-up H2) or the heuristic Hn needed.     *)
(*                                                                            *)
(* exp_add         -                                         core             *)
(* exp_lin_ln      0 < x                                     core             *)
(* exp_ln_add      0 < x, 0 < y                              core             *)
(* exp_opp         -                                         core             *)
(* exp_cosh_sinh   -                                         core             *)
(* exp_double      -                                         core             *)
(* exp_m2          -                                         core             *)
(* exp_sub3        -                                         core             *)
(* exp_sqrt        -                                         core             *)
(* exp_half_sq     -                                         core             *)
(* exp_half_div    exp (x * / (1 + 1)) <> 1                  core             *)
(* exp_third_cube  -                                         core             *)
(* exp_add1        -                                         core             *)
(* exp_add2        -                                         core             *)
(* exp_frac        x + 1 <> 0                                core             *)
(* exp_exp2        -                                         core             *)
(* exp_exp_add     -                                         core             *)
(* exp_2third      -                                         core             *)
(* exp_lcm         -                                         core             *)
(* exp_frac_sum    x + 1 <> 0                                H1               *)
(* exp_xx          x <> 0                                    core             *)
(* exp_frac_sq     x + 1 <> 0                                core             *)
(* exp_half_one    -                                         core             *)
(* exp_merge       -                                         core             *)
(* exp_three       -                                         core             *)
(* exp_three_frac  x - 1 <> 0, a + b <> 0                    core             *)
(* exp_frac3       x + y <> 0                                core             *)
(* exp_two_levels  -                                         core             *)
(* exp_four        -                                         core             *)
(* exp_ln_half     0 < x                                     core             *)
(* ln_exp_mul      -                                         core             *)
(* ln_sq_pos       0 < x                                     core             *)
(* ln_div_pos      0 < y, 0 < x                              core             *)
(* ln_mul_exp      0 < x                                     core             *)
(* ln_6            -                                         core             *)
(* ln_8            -                                         core             *)
(* ln_12           -                                         core             *)
(* ln_inv4         -                                         core             *)
(* ln_3_4          -                                         core             *)
(* ln_sq_m1        0 < x - 1                                 core             *)
(* ln_sq_p1        0 < x + 1                                 core             *)
(* ln_mul_sub      0 < x * y, 0 < x                          core             *)
(* ln_sq_exp       0 < x                                     core             *)
(* ln_exp_sq       -                                         core             *)
(* ln_diff_sq      0 < x ^ 2 - y ^ 2, 0 < x - y              core             *)
(* ln_2x2          0 < 2 * x + 2                             core             *)
(* ln_1_sq         0 < 1 - x ^ 2                             core             *)
(* ln_xy_x         0 < x * y + x, 0 < x                      core             *)
(* ln_cube         0 < x - 1                                 core             *)
(* ln_1024         -                                         core             *)
(* ln_1024b        -                                         core             *)
(* ln_sq_abs       x <> 0                                    core             *)
(* ln_quot         0 < x - 1                                 core             *)
(* ln_abs_quot     x + y <> 0, x - y <> 0                    core             *)
(* ln_ln_sq        0 < x, ln x <> 0                          core             *)
(* ln_neg_arg      0 < exp x * (1 - exp x) / (exp x - 1) ^ 3 core [1]         *)
(* cosh_sinh       -                                         core             *)
(* cosh_double     -                                         H1               *)
(* sinh_double     -                                         core             *)
(* sinh_add        -                                         core             *)
(* cosh_add        -                                         core             *)
(* tanh_add        -                                         H1               *)
(* rpower_thirds   0 < x                                     core             *)
(* rpower_2        0 < x                                     core             *)
(* rpower_rpower   0 < x                                     core             *)
(* rpower_add      0 < x                                     core             *)
(* rpower_halves   0 < x                                     core             *)
(* rpower_sqrt     0 < x                                     core             *)
(* rlog_2_8        -                                         core             *)
(* rlog_cube       ln x <> 0, 0 < x ^ 3                      core             *)
(* trig_damped     -                                         core             *)
(* trig_sum        -                                         core             *)
(* trig_integral   -                                         core             *)
(* trig_cosh       -                                         core             *)
(* trig_exp_ln_cos 0 < cos x                                 core             *)
(* trig_ln_tan     0 < sin x, 0 < cos x                      core             *)
(* trig_ln_pyth    -                                         H3               *)
(* trig_exp_pyth   -                                         H3               *)
(* trig_ln_double  0 < cos x                                 H3               *)
(* ln_sqrt_half   0 < x                                     H5               *)
(* ln_x_sqrt      0 < x, 0 < y (with hypotheses: -)        H5               *)
(*                                                                            *)
(* [1] the argument is negative for every x (it is - exp x / (exp x - 1) ^ 2), *)
(*     so the condition never holds: explog proves the (false for Stdlib's    *)
(*     ln) equality only under an unsatisfiable condition, which is sound.    *)
(******************************************************************************)
From RadcanExpLog Require Import ExpLogTac.
Local Open Scope R_scope.

(* the first remaining goal is P (syntactically) *)
Ltac left_is P := lazymatch goal with |- P => idtac end.

(* ------------------------------------------------------------------------- *)
(* exp (Theorem 5.7(b): linear algebra over Q on exp arguments)              *)
(* ------------------------------------------------------------------------- *)

Lemma exp_add x y : exp (x + y) = exp x * exp y.
Proof. explog. Qed.

Lemma exp_lin_ln x (h1 : 0 < x) : exp (2 * x + 3 * ln x) = x ^ 3 * exp x ^ 2.
Proof. explog. Qed.
Goal forall x, exp (2 * x + 3 * ln x) = x ^ 3 * exp x ^ 2.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma exp_ln_add x y (h1 : 0 < x) (h2 : 0 < y) : exp (ln x + ln y) = x * y.
Proof. explog. Qed.
Goal forall x y, exp (ln x + ln y) = x * y.
Proof. intros. explog; [> left_is (0 < x) | left_is (0 < y) ]. Abort.

Lemma exp_opp x : exp x * exp (- x) = 1.
Proof. explog. Qed.

Lemma exp_cosh_sinh x : (exp x + exp (- x)) ^ 2 - (exp x - exp (- x)) ^ 2 = 4.
Proof. explog. Qed.

Lemma exp_double x : exp (2 * x) - 1 = (exp x - 1) * (exp x + 1).
Proof. explog. Qed.

Lemma exp_m2 x : exp (- 2 * x) * exp x ^ 2 = 1.
Proof. explog. Qed.

Lemma exp_sub3 x y : exp (x - 3 * y) = exp x / exp y ^ 3.
Proof. explog. Qed.

Lemma exp_sqrt x : exp (x / 2) = sqrt (exp x).
Proof. explog. Qed.

Lemma exp_half_sq x : exp (x / 2) ^ 2 = exp x.
Proof. explog. Qed.

Lemma exp_half_div x (h1 : x <> 0) : (exp x - 1) / (exp (x / 2) - 1) = exp (x / 2) + 1.
Proof. explog. move=> e; apply: h1; have := f_equal ln e; rewrite ln_exp ln_1; lra. Qed.
Goal forall x, (exp x - 1) / (exp (x / 2) - 1) = exp (x / 2) + 1.
Proof. intros. explog; [> left_is (exp (x * / (1 + 1)) <> 1) ]. Abort.

Lemma exp_third_cube x : exp (x / 3) ^ 3 = exp x.
Proof. explog. Qed.

Lemma exp_add1 x : exp (x + 1) = exp 1 * exp x.
Proof. explog. Qed.

Lemma exp_add2 x : exp (2 + x) = exp 1 ^ 2 * exp x.
Proof. explog. Qed.

Lemma exp_frac x (h1 : x + 1 <> 0) : exp (x / (x + 1)) * exp (1 / (x + 1)) = exp 1.
Proof. explog. Qed.
Goal forall x, exp (x / (x + 1)) * exp (1 / (x + 1)) = exp 1.
Proof. intros. explog; [> left_is (x + 1 <> 0) ]. Abort.

Lemma exp_exp2 x : exp (exp x) * exp (exp x) = exp (2 * exp x).
Proof. explog. Qed.

Lemma exp_exp_add x : exp (x + exp x) = exp x * exp (exp x).
Proof. explog. Qed.

Lemma exp_2third x : exp (2 * x / 3) = exp (x / 3) ^ 2.
Proof. explog. Qed.

Lemma exp_lcm x : exp (x / 2) * exp (x / 3) = exp (5 * x / 6).
Proof. explog. Qed.

Lemma exp_frac_sum x (h1 : x + 1 <> 0) : (exp (x / (x + 1)) + 1) * exp (1 / (x + 1)) = exp 1 + exp (1 / (x + 1)).
Proof. explog. Qed.
Goal forall x, (exp (x / (x + 1)) + 1) * exp (1 / (x + 1)) = exp 1 + exp (1 / (x + 1)).
Proof. intros. explog; [> left_is (x + 1 <> 0) ]. Abort.

Lemma exp_xx x (h1 : x <> 0) : exp (x / x) = exp 1.
Proof. explog. Qed.
Goal forall x, exp (x / x) = exp 1.
Proof. intros. explog; [> left_is (x <> 0) ]. Abort.

Lemma exp_frac_sq x (h1 : x + 1 <> 0) : exp (x / (x + 1)) ^ 2 * exp (2 / (x + 1)) = exp 1 ^ 2.
Proof. explog. Qed.
Goal forall x, exp (x / (x + 1)) ^ 2 * exp (2 / (x + 1)) = exp 1 ^ 2.
Proof. intros. explog; [> left_is (x + 1 <> 0) ]. Abort.

Lemma exp_half_one : exp (1 / 2) ^ 2 = exp 1.
Proof. explog. Qed.

Lemma exp_merge x : (exp (x / 2) + 1) ^ 2 = exp (x / 3) ^ 3 + 2 * exp (x / 2) + 1.
Proof. explog. Qed.

Lemma exp_three x : exp (x / 2) * exp (x / 3) * exp (x / 6) = exp x.
Proof. explog. Qed.

Lemma exp_three_frac a b x (h1 : x - 1 <> 0) (h2 : a + b <> 0) : exp (a / (a + b)) * exp (b / (a + b)) * exp (1 / (x - 1) - x / (x - 1)) = 1.
Proof. explog. Qed.
Goal forall a b x, exp (a / (a + b)) * exp (b / (a + b)) * exp (1 / (x - 1) - x / (x - 1)) = 1.
Proof. intros. explog; [> left_is (x - 1 <> 0) | left_is (a + b <> 0) ]. Abort.

Lemma exp_frac3 x y (h1 : x + y <> 0) : exp (x / (x + y)) * exp (y / (x + y)) * exp (x / 3) ^ 3 = exp (1 + x).
Proof. explog. Qed.
Goal forall x y, exp (x / (x + y)) * exp (y / (x + y)) * exp (x / 3) ^ 3 = exp (1 + x).
Proof. intros. explog; [> left_is (x + y <> 0) ]. Abort.

Lemma exp_two_levels x : exp (exp (2 * x)) * exp (- exp x ^ 2) = 1.
Proof. explog. Qed.

Lemma exp_four x : exp (x / 2) * exp (x / 3) * exp (x / 5) * exp (x / 7) = exp (247 * x / 210).
Proof. explog. Qed.

Lemma exp_ln_half x (h1 : 0 < x) : exp (ln x / 2) ^ 2 = x.
Proof. explog. Qed.
Goal forall x, exp (ln x / 2) ^ 2 = x.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

(* ------------------------------------------------------------------------- *)
(* ln (Theorem 5.7(a): factorisation of ln arguments, ln |p|)                *)
(* ------------------------------------------------------------------------- *)

Lemma ln_exp_mul x y : ln (exp x * exp y) = x + y.
Proof. explog. Qed.

Lemma ln_sq_pos x (h1 : 0 < x) : ln (x ^ 2) = 2 * ln x.
Proof. explog. Qed.
Goal forall x, ln (x ^ 2) = 2 * ln x.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma ln_div_pos x y (h1 : 0 < x) (h2 : 0 < y) : ln (x / y) + ln y = ln x.
Proof. explog. Qed.
Goal forall x y, ln (x / y) + ln y = ln x.
Proof. intros. explog; [> left_is (0 < y) | left_is (0 < x) ]. Abort.

Lemma ln_mul_exp x (h1 : 0 < x) : ln (x * exp x) = ln x + x.
Proof. explog. Qed.
Goal forall x, ln (x * exp x) = ln x + x.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma ln_6 : ln 6 = ln 2 + ln 3.
Proof. explog. Qed.

Lemma ln_8 : ln 8 = 3 * ln 2.
Proof. explog. Qed.

Lemma ln_12 : ln 12 - ln 3 = 2 * ln 2.
Proof. explog. Qed.

Lemma ln_inv4 : ln (/ 4) = - 2 * ln 2.
Proof. explog. Qed.

Lemma ln_3_4 : ln (3 / 4) = ln 3 - 2 * ln 2.
Proof. explog. Qed.

Lemma ln_sq_m1 x (h1 : 1 < x) : ln (x ^ 2 - 1) - ln (x - 1) - ln (x + 1) = 0.
Proof. explog. Qed.
Goal forall x, ln (x ^ 2 - 1) - ln (x - 1) - ln (x + 1) = 0.
Proof. intros. explog; [> left_is (0 < x - 1) ]. Abort.

Lemma ln_sq_p1 x (h1 : 0 < x + 1) : ln (x ^ 2 + 2 * x + 1) = 2 * ln (x + 1).
Proof. explog. Qed.
Goal forall x, ln (x ^ 2 + 2 * x + 1) = 2 * ln (x + 1).
Proof. intros. explog; [> left_is (0 < x + 1) ]. Abort.

Lemma ln_mul_sub x y (h1 : 0 < x) (h2 : 0 < y) : ln (x * y) - ln x = ln y.
Proof. explog. Qed.
Goal forall x y, ln (x * y) - ln x = ln y.
Proof. intros. explog; [> left_is (0 < x * y) | left_is (0 < x) ]. Abort.

Lemma ln_sq_exp x y (h1 : 0 < x) : ln (x ^ 2 * exp y) = 2 * ln x + y.
Proof. explog. Qed.
Goal forall x y, ln (x ^ 2 * exp y) = 2 * ln x + y.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma ln_exp_sq x : ln (exp x ^ 2 + 2 * exp x + 1) = 2 * ln (exp x + 1).
Proof. explog. Qed.

Lemma ln_diff_sq x y (h1 : 0 < x - y) (h2 : 0 < x + y) : ln (x ^ 2 - y ^ 2) - ln (x - y) = ln (y + x).
Proof. explog. Qed.
Goal forall x y, ln (x ^ 2 - y ^ 2) - ln (x - y) = ln (y + x).
Proof. intros. explog; [> left_is (0 < x ^ 2 - y ^ 2) | left_is (0 < x - y) ]. Abort.

Lemma ln_2x2 x (h1 : 0 < x + 1) : ln (2 * x + 2) = ln 2 + ln (x + 1).
Proof. explog. Qed.
Goal forall x, ln (2 * x + 2) = ln 2 + ln (x + 1).
Proof. intros. explog; [> left_is (0 < 2 * x + 2) ]. Abort.

Lemma ln_1_sq x (h1 : 0 < 1 - x) (h2 : 0 < 1 + x) : ln (1 - x ^ 2) = ln (1 - x) + ln (1 + x).
Proof. explog. Qed.
Goal forall x, ln (1 - x ^ 2) = ln (1 - x) + ln (1 + x).
Proof. intros. explog; [> left_is (0 < 1 - x ^ 2) ]. Abort.

Lemma ln_xy_x x y (h1 : 0 < x) (h2 : 0 < y + 1) : ln (x * y + x) = ln x + ln (y + 1).
Proof. explog. Qed.
Goal forall x y, ln (x * y + x) = ln x + ln (y + 1).
Proof. intros. explog; [> left_is (0 < x * y + x) | left_is (0 < x) ]. Abort.

Lemma ln_cube x (h1 : 1 < x) : ln (x ^ 3 - 1) = ln (x - 1) + ln (x ^ 2 + x + 1).
Proof. explog. Qed.
Goal forall x, ln (x ^ 3 - 1) = ln (x - 1) + ln (x ^ 2 + x + 1).
Proof. intros. explog; [> left_is (0 < x - 1) ]. Abort.

Lemma ln_1024 : ln 1024 + ln (/ 1000) = 7 * ln 2 - 3 * ln 5.
Proof. explog. Qed.

Lemma ln_1024b : ln 1024 + ln (/ 1000) = 10 * ln 2 - 3 * ln 2 - 3 * ln 5.
Proof. explog. Qed.

Lemma ln_sq_abs x (h1 : x <> 0) : ln (x ^ 2) = 2 * ln (Rabs x).
Proof. explog. Qed.
Goal forall x, ln (x ^ 2) = 2 * ln (Rabs x).
Proof. intros. explog; [> left_is (x <> 0) ]. Abort.

Lemma ln_quot x (h1 : 1 < x) : ln ((x + 1) / (x - 1)) = ln (x + 1) - ln (x - 1).
Proof. explog. Qed.
Goal forall x, ln ((x + 1) / (x - 1)) = ln (x + 1) - ln (x - 1).
Proof. intros. explog; [> left_is (0 < x - 1) ]. Abort.

Lemma ln_abs_quot x y (h1 : x + y <> 0) (h2 : x - y <> 0) : ln (Rabs ((x ^ 2 - y ^ 2) / (x + y) ^ 3)) = ln (Rabs (y - x)) - 2 * ln (Rabs (x + y)).
Proof. explog. Qed.
Goal forall x y, ln (Rabs ((x ^ 2 - y ^ 2) / (x + y) ^ 3)) = ln (Rabs (y - x)) - 2 * ln (Rabs (x + y)).
Proof. intros. explog; [> left_is (x + y <> 0) | left_is (x - y <> 0) ]. Abort.

Lemma ln_ln_sq x (h1 : 0 < x) (h2 : ln x <> 0) : ln (ln x ^ 2) = 2 * ln (Rabs (ln x)).
Proof. explog. Qed.
Goal forall x, ln (ln x ^ 2) = 2 * ln (Rabs (ln x)).
Proof. intros. explog; [> left_is (0 < x) | left_is (ln x <> 0) ]. Abort.

Goal forall x, ln (exp x * (1 - exp x) / (exp x - 1) ^ 3) = x - 2 * ln (Rabs (1 - exp x)).
Proof. intros. explog; [> left_is (0 < exp x * (1 - exp x) / (exp x - 1) ^ 3) ]. Abort.

(* ------------------------------------------------------------------------- *)
(* hyperbolic functions, Rpower, Rlog (unfolded to exp / ln)                 *)
(* ------------------------------------------------------------------------- *)

Lemma cosh_sinh x : cosh x ^ 2 - sinh x ^ 2 = 1.
Proof. explog. Qed.

Lemma cosh_double x : cosh (2 * x) = 2 * cosh x ^ 2 - 1.
Proof. explog. Qed.

Lemma sinh_double x : sinh (2 * x) = 2 * sinh x * cosh x.
Proof. explog. Qed.

Lemma sinh_add x y : sinh (x + y) = sinh x * cosh y + cosh x * sinh y.
Proof. explog. Qed.

Lemma cosh_add x y : cosh (x + y) = cosh x * cosh y + sinh x * sinh y.
Proof. explog. Qed.

Lemma tanh_add x y : tanh (x + y) = (tanh x + tanh y) / (1 + tanh x * tanh y).
Proof. explog. Qed.

Lemma rpower_thirds x (h1 : 0 < x) : Rpower x (1/3) * Rpower x (2/3) = x.
Proof. explog. Qed.
Goal forall x, Rpower x (1/3) * Rpower x (2/3) = x.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma rpower_2 x (h1 : 0 < x) : Rpower x 2 = x ^ 2.
Proof. explog. Qed.
Goal forall x, Rpower x 2 = x ^ 2.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma rpower_rpower x y z (h1 : 0 < x) : Rpower (Rpower x y) z = Rpower x (y * z).
Proof. explog. Qed.
Goal forall x y z, Rpower (Rpower x y) z = Rpower x (y * z).
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma rpower_add x y z (h1 : 0 < x) : Rpower x y * Rpower x z = Rpower x (y + z).
Proof. explog. Qed.
Goal forall x y z, Rpower x y * Rpower x z = Rpower x (y + z).
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma rpower_halves x (h1 : 0 < x) : Rpower x (-1/2) * Rpower x (1/2) = 1.
Proof. explog. Qed.
Goal forall x, Rpower x (-1/2) * Rpower x (1/2) = 1.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma rpower_sqrt x (h1 : 0 < x) : Rpower x (1/2) = sqrt x.
Proof. explog. Qed.
Goal forall x, Rpower x (1/2) = sqrt x.
Proof. intros. explog; [> left_is (0 < x) ]. Abort.

Lemma rlog_2_8 : Rlog 2 8 = 3.
Proof. explog. Qed.

Lemma rlog_cube x (h1 : 0 < x) (h2 : x <> 1) : Rlog x (x ^ 3) = 3.
Proof. explog. move=> e; apply: h2; by rewrite -(exp_ln x h1) e exp_0. Qed.
Goal forall x, Rlog x (x ^ 3) = 3.
Proof. intros. explog; [> left_is (ln x <> 0) | left_is (0 < x ^ 3) ]. Abort.

(* ------------------------------------------------------------------------- *)
(* mixed with trigonometry (zero test radcan_trig; H3 on trig arguments)     *)
(* ------------------------------------------------------------------------- *)

Lemma trig_damped x : exp x * sin (2 * x) = 2 * exp x * sin x * cos x.
Proof. explog. Qed.

Lemma trig_sum x y : exp (x + y) * cos (x + y) = exp x * exp y * (cos x * cos y - sin x * sin y).
Proof. explog. Qed.

Lemma trig_integral x : exp x * (sin x + cos x) / 2 + exp x * (cos x - sin x) / 2 = exp x * cos x.
Proof. explog. Qed.

Lemma trig_cosh x y : cosh x ^ 2 * cos y ^ 2 + sinh x ^ 2 * sin y ^ 2 = cosh x ^ 2 - sin y ^ 2.
Proof. explog. Qed.

Lemma trig_exp_ln_cos x (h1 : 0 < cos x) : exp (2 * ln (cos x)) = cos x ^ 2.
Proof. explog. Qed.
Goal forall x, exp (2 * ln (cos x)) = cos x ^ 2.
Proof. intros. explog; [> left_is (0 < cos x) ]. Abort.

Lemma trig_ln_tan x (h1 : 0 < sin x) (h2 : 0 < cos x) : ln (tan x) = ln (sin x) - ln (cos x).
Proof. explog. Qed.
Goal forall x, ln (tan x) = ln (sin x) - ln (cos x).
Proof. intros. explog; [> left_is (0 < sin x) | left_is (0 < cos x) ]. Abort.

Lemma trig_ln_pyth x : ln (cos x ^ 2 + sin x ^ 2) = 0.
Proof. explog. Qed.

Lemma trig_exp_pyth x : exp (sin x ^ 2) * exp (cos x ^ 2) = exp 1.
Proof. explog. Qed.

Lemma trig_ln_double x (h1 : 0 < cos x) : ln (1 + cos (2 * x)) = ln 2 + 2 * ln (cos x).
Proof. explog. Qed.
Goal forall x, ln (1 + cos (2 * x)) = ln 2 + 2 * ln (cos x).
Proof. intros. explog; [> left_is (0 < cos x) ]. Abort.

(* ------------------------------------------------------------------------- *)
(* must fail (false, or relations between constants outside 5.7)             *)
(* ------------------------------------------------------------------------- *)

Goal exp 1 = 3.
Proof. Fail explog. Abort.

Goal forall x, exp x = x.
Proof. intros. Fail explog. Abort.

Goal forall x, exp (x / (x + 1)) = exp 1.
Proof. intros. Fail explog. Abort.

Goal forall x, cosh x = sinh x.
Proof. intros. Fail explog. Abort.

Goal forall x y, exp (x + y) = exp x.
Proof. intros. Fail explog. Abort.

Goal Rlog 2 3 = 1.
Proof. Fail explog. Abort.

Goal ln 2 = 1.
Proof. Fail explog. Abort.

Goal ln 2 + ln 3 = ln 5.
Proof. Fail explog. Abort.

Goal forall x, ln (x ^ 2 + 1) = 2 * ln x.
Proof. intros. Fail explog. Abort.

(* square roots inside ln: the core treats sqrt x as an atom (TR223
   excludes the algebraic case); heuristic H5 relates ln |sqrt a| to ln |a| *)
Lemma ln_sqrt_half x : 0 < x -> ln (sqrt x) = ln x / 2.
Proof. move=> hx. explog. Qed.

Goal forall x, ln (sqrt x) = ln x / 2.
Proof. intros. explog. Show. Abort.

Lemma ln_x_sqrt x y : 0 < x -> 0 < y -> ln (x * sqrt y) = ln x + ln y / 2.
Proof. move=> hx hy. explog. Qed.
