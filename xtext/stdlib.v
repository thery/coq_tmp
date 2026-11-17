(* Stdlib lemmas explained directly from the library (no copy of the proofs). *)
From Stdlib Require Import Arith Bool List.
From XText Require Import Explain.

(* List *)
Time Explain app_assoc to "examples/std_app_assoc.md".
Time Explain app_nil_r to "examples/std_app_nil_r.md".
Time Explain app_comm_cons to "examples/std_app_comm_cons.md".
Time Explain rev_involutive to "examples/std_rev_involutive.md".
Time Explain rev_app_distr to "examples/std_rev_app_distr.md".
Time Explain length_rev to "examples/std_length_rev.md".
Time Explain map_app to "examples/std_map_app.md".
Time Explain map_map to "examples/std_map_map.md".
Time Explain length_app to "examples/std_length_app.md".
Time Explain in_app_or to "examples/std_in_app_or.md".
Time Explain in_or_app to "examples/std_in_or_app.md".
Time Explain in_map to "examples/std_in_map.md".
Time Explain in_eq to "examples/std_in_eq.md".
Time Explain in_cons to "examples/std_in_cons.md".

(* Nat *)
Time Explain Nat.add_comm to "examples/std_Nat_add_comm.md".
Time Explain Nat.add_assoc to "examples/std_Nat_add_assoc.md".
Time Explain Nat.mul_comm to "examples/std_Nat_mul_comm.md".
Time Explain Nat.le_trans to "examples/std_Nat_le_trans.md".
Time Explain Nat.add_0_r to "examples/std_Nat_add_0_r.md".
Time Explain Nat.add_succ_r to "examples/std_Nat_add_succ_r.md".
Time Explain Nat.le_refl to "examples/std_Nat_le_refl.md".
Time Explain Nat.lt_irrefl to "examples/std_Nat_lt_irrefl.md".
Time Explain Nat.mul_1_r to "examples/std_Nat_mul_1_r.md".
Time Explain Nat.pred_succ to "examples/std_Nat_pred_succ.md".
Time Explain plus_n_O to "examples/std_plus_n_O.md".
Time Explain plus_n_Sm to "examples/std_plus_n_Sm.md".

(* Bool *)
Time Explain andb_comm to "examples/std_andb_comm.md".
Time Explain orb_comm to "examples/std_orb_comm.md".
Time Explain negb_involutive to "examples/std_negb_involutive.md".
Time Explain andb_true_r to "examples/std_andb_true_r.md".
Time Explain orb_false_r to "examples/std_orb_false_r.md".
Time Explain andb_assoc to "examples/std_andb_assoc.md".
Time Explain negb_andb to "examples/std_negb_andb.md".

(* Logic *)
Time Explain and_comm to "examples/std_and_comm.md".
Time Explain or_comm to "examples/std_or_comm.md".
Time Explain and_assoc to "examples/std_and_assoc.md".
Time Explain or_assoc to "examples/std_or_assoc.md".
Time Explain eq_sym to "examples/std_eq_sym.md".
Time Explain eq_trans to "examples/std_eq_trans.md".
Time Explain f_equal to "examples/std_f_equal.md".
