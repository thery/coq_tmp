// The proof text plus_n_Sm', written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("plus_n_Sm'", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Let "#var("n m : nat")#". We prove "#claim("S (n + m) = n + S m")#"."]

#steps((
  step("1", [#"To prove "#fact("S (n + m) = n + S m")#" by induction (nat, nat_ind), we generalise it to "#fact("forall n0 : nat, S (n0 + m) = n0 + S m")#":"], ()),
  step("2", [#"Case 1 (base): we prove "#claim("0 + S m = 0 + S m")#"."], (
    step("2.1", [#"By definition of eq (eq_refl), we have "#claim("0 + S m = 0 + S m")#" "#by("Corelib.Init.Logic.eq_refl")#"."], ()),
  )),
  step("3", [#"Case 2 (inductive): we prove "#claim("forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m")#"."], (
    step("3.1", [#"Let us choose arbitrarily "#var("n0 : nat")#"; assume by induction hypothesis "#hyp("S (n0 + m) = n0 + S m")#" "#name("IH")#"."], (
      step("3.1.1", [#"By definition of eq (eq_refl), we have "#claim("S (n0 + S m) = S (n0 + S m)")#" "#by("Corelib.Init.Logic.eq_refl")#"."], ()),
      step("3.1.2", [#"By IH we have "#claim("S (n0 + m) = n0 + S m")#"."], ()),
      step("3.1.3", [#"Rewriting with "#fact("S (n0 + m) = n0 + S m")#" from right to left (eq_ind_r), we get "#claim("S (S (n0 + m)) = S (n0 + S m)")#"."], ()),
    )),
  )),
  step("4", [#"These cases being exhaustive, we deduce "#claim("forall n0 : nat, S (n0 + m) = n0 + S m")#" "#by("Corelib.Init.Datatypes.nat_ind")#"."], ()),
  step("5", [#"In particular "#claim("S (n + m) = n + S m")#"."], ()),
))
