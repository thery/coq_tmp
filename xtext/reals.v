(* A text about real numbers, for the formulas in mathematics of its PDF
   (fractions, powers, square roots, absolute values): ../prooftext/pdf.sh
   examples/reals_sqrt_sq.md. *)
From Stdlib Require Import Reals.
From XText Require Import Explain.
Open Scope R_scope.

(* the require line of the texts: the reals, their notations and scope *)
Elpi Accumulate xtext.db lp:{{
  :before "xtext-header-require"
  xtext-header-require "From Stdlib Require Import Reals. Open Scope R_scope.".
}}.

Lemma reals_sqrt_sq (x y : R) (H : 0 <= x) :
  sqrt (x ^ 2) / (Rabs y + 1) = x / (Rabs y + 1).
Proof. rewrite <- Rsqr_pow2, (sqrt_Rsqr x H). reflexivity. Qed.

Lemma reals_exp_div (x : R) : 0 < exp x / (1 + x ^ 2).
Proof.
  exact (Rdiv_lt_0_compat _ _ (exp_pos x)
           (Rplus_lt_le_0_compat _ _ Rlt_0_1 (pow2_ge_0 x))).
Qed.

Explain reals_sqrt_sq to "examples/reals_sqrt_sq.md".
Explain reals_exp_div to "examples/reals_exp_div.md".
