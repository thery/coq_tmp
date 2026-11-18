// The proof text le_n_S', written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("le_n_S'", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Let "#var("n m : nat")#". Assume "#hyp("n <= m")#" "#name("H")#". We prove "#claim("S n <= S m")#"."]

#steps((
  step("1", [#"We prove "#fact("S n <= S m")#" by induction on "#fact("n <= m")#" "#name("H")#" (le, le_ind):"], ()),
  step("2", [#"Case 1 (base): we prove "#claim("S n <= S n")#"."], (
    step("2.1", [#"By definition of le (le_n), we have "#claim("S n <= S n")#" "#by("Corelib.Init.Peano.le_n")#"."], ()),
  )),
  step("3", [#"Case 2 (inductive): we prove "#claim("forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)")#"."], (
    step("3.1", [#"Let us choose arbitrarily "#var("m0 : nat")#"; assume "#hyp("n <= m0")#" "#name("H0")#" and by induction hypothesis "#hyp("S n <= S m0")#" "#name("IH")#"."], (
      step("3.1.1", [#"By definition of le (le_S) with witness "#fact("S m0")#", from "#fact("S n <= S m0")#" "#name("IH")#" we deduce "#claim("S n <= S (S m0)")#" "#by("Corelib.Init.Peano.le_S")#"."], ()),
    )),
  )),
  step("4", [#"We have "#claim("S n <= S m")#" in all cases."], ()),
))
