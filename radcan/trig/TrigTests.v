(******************************************************************************)
(* TrigTests: the target identities of radcan_trig (TrigTac.v).              *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From RadcanTrig Require Import TrigTac.

Local Open Scope R_scope.

Lemma t_cosD x y : cos (x + y) = cos x * cos y - sin x * sin y.
Proof. radcan_trig. Qed.

Lemma t_sinD x y : sin (x + y) = sin x * cos y + cos x * sin y.
Proof. radcan_trig. Qed.

Lemma t_pyth x : sin x ^ 2 + cos x ^ 2 = 1.
Proof. radcan_trig. Qed.

Lemma t_cos3 x : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x.
Proof. radcan_trig. Qed.

Lemma t_sin2 x : sin (2 * x) = 2 * sin x * cos x.
Proof. radcan_trig. Qed.

Lemma t_cdiff x y : cos (x + y) * cos (x - y) = cos x ^ 2 - sin y ^ 2.
Proof. radcan_trig. Qed.

Lemma t_prod x y : cos x * cos y = (cos (x - y) + cos (x + y)) / 2.
Proof. radcan_trig. Qed.

(* the three conditions are closed from the hypotheses *)
Lemma t_tanD x y : cos x <> 0 -> cos y <> 0 -> cos (x + y) <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof. intros hx hy hxy. radcan_trig. Qed.

(* without hypotheses, the conditions are left, on R *)
Goal forall x y, tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
intros x y. radcan_trig.
(* 4 goals: cos y <> 0, cos x <> 0, cos x * cos y - sin x * sin y <> 0,
   cos (x + y) <> 0 *)
Abort.

Lemma t_cos3PI : cos (PI / 3) = 1 / 2.
Proof. radcan_trig. Qed.

Lemma t_cos5PI : cos (PI / 5) = (1 + sqrt 5) / 4.
Proof. radcan_trig. Qed.

Lemma t_imo1963 :
  cos (PI / 7) - cos (2 * PI / 7) + cos (3 * PI / 7) = 1 / 2.
Proof. radcan_trig. Qed.

Lemma t_shift x :
  sin (x + PI / 7) = sin x * cos (PI / 7) + cos x * sin (PI / 7).
Proof. radcan_trig. Qed.

(* a false identity is refused *)
Goal forall x, cos (2 * x) = 2 * cos x - 1.
Proof. intros x. Fail radcan_trig. Abort.
