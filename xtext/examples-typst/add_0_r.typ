// The proof text add_0_r', written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("add_0_r'", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Let "#var($n ∈ ℕ$)#". We prove "#claim($n + 0 = n$)#"."]

#steps((
  step("1", [#"We prove "#fact($n + 0 = n$)#" by induction on "#fact($n$)#" ("#cited("nat", "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat")#", "#cited("nat_ind", "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat_ind")#"):"], ()),
  step("2", [#"Case 1 (base): we prove "#claim($0 = 0$)#"."], (
    step("2.1", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($0 = 0$)#" "#by("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], ()),
  )),
  step("3", [#"Case 2 (inductive): we prove "#claim($∀ m ∈ ℕ , m + 0 = m → "S"\(m\) + 0 = "S"\(m\)$)#"."], (
    step("3.1", [#"Let us choose arbitrarily "#var($m ∈ ℕ$)#"; assume by induction hypothesis "#hyp($m + 0 = m$)#" "#name("IH", label: "3.1:IH")#"."], (
      step("3.1.1", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($"S"\(m\) = "S"\(m\)$)#" "#by("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], ()),
      step("3.1.2", [#"By "#named("IH", "3.1:IH")#" we have "#claim($m + 0 = m$)#"."], ()),
      step("3.1.3", [#"Rewriting with "#fact($m + 0 = m$)#" from right to left ("#cited("eq_ind_r", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_ind_r")#"), we get "#claim($"S"\(m + 0\) = "S"\(m\)$)#"."], ()),
    )),
  )),
  step("4", [#"These cases being exhaustive, we deduce "#claim($n + 0 = n$)#" "#by("Corelib.Init.Datatypes.nat_ind", url: "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat_ind")#"."], ()),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"),))
