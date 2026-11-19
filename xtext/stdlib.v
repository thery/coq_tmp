(* Stdlib lemmas explained directly from the library (no copy of the proofs). *)
From Stdlib Require Import Arith Bool List.
From XText Require Import ExtractText.

(* List *)
Time ExtractText app_assoc to "examples/std_app_assoc.md".
Time ExtractText app_nil_r to "examples/std_app_nil_r.md".
Time ExtractText app_comm_cons to "examples/std_app_comm_cons.md".
Time ExtractText rev_involutive to "examples/std_rev_involutive.md".
Time ExtractText rev_app_distr to "examples/std_rev_app_distr.md".
Time ExtractText length_rev to "examples/std_length_rev.md".
Time ExtractText map_app to "examples/std_map_app.md".
Time ExtractText map_map to "examples/std_map_map.md".
Time ExtractText length_app to "examples/std_length_app.md".
Time ExtractText in_app_or to "examples/std_in_app_or.md".
Time ExtractText in_or_app to "examples/std_in_or_app.md".
Time ExtractText in_map to "examples/std_in_map.md".
Time ExtractText in_eq to "examples/std_in_eq.md".
Time ExtractText in_cons to "examples/std_in_cons.md".

(* Nat *)
Time ExtractText Nat.add_comm to "examples/std_Nat_add_comm.md".
Time ExtractText Nat.add_assoc to "examples/std_Nat_add_assoc.md".
Time ExtractText Nat.mul_comm to "examples/std_Nat_mul_comm.md".
Time ExtractText Nat.le_trans to "examples/std_Nat_le_trans.md".
Time ExtractText Nat.add_0_r to "examples/std_Nat_add_0_r.md".
Time ExtractText Nat.add_succ_r to "examples/std_Nat_add_succ_r.md".
Time ExtractText Nat.le_refl to "examples/std_Nat_le_refl.md".
Time ExtractText Nat.lt_irrefl to "examples/std_Nat_lt_irrefl.md".
Time ExtractText Nat.mul_1_r to "examples/std_Nat_mul_1_r.md".
Time ExtractText Nat.pred_succ to "examples/std_Nat_pred_succ.md".
Time ExtractText plus_n_O to "examples/std_plus_n_O.md".
Time ExtractText plus_n_Sm to "examples/std_plus_n_Sm.md".

(* Bool *)
Time ExtractText andb_comm to "examples/std_andb_comm.md".
Time ExtractText orb_comm to "examples/std_orb_comm.md".
Time ExtractText negb_involutive to "examples/std_negb_involutive.md".
Time ExtractText andb_true_r to "examples/std_andb_true_r.md".
Time ExtractText orb_false_r to "examples/std_orb_false_r.md".
Time ExtractText andb_assoc to "examples/std_andb_assoc.md".
Time ExtractText negb_andb to "examples/std_negb_andb.md".

(* Logic *)
Time ExtractText and_comm to "examples/std_and_comm.md".
Time ExtractText or_comm to "examples/std_or_comm.md".
Time ExtractText and_assoc to "examples/std_and_assoc.md".
Time ExtractText or_assoc to "examples/std_or_assoc.md".
Time ExtractText eq_sym to "examples/std_eq_sym.md".
Time ExtractText eq_trans to "examples/std_eq_trans.md".
Time ExtractText f_equal to "examples/std_f_equal.md".
