// The proof text le_n_S', written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("le_n_S'", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Let "#var($n , m ∈ ℕ$)#". Assume "#hyp($n ≤ m$)#" "#name("H", label: "statement:H")#". We prove "#claim($"S"\(n\) ≤ "S"\(m\)$)#"."]

#steps((
  step("1", [#"We prove "#fact($"S"\(n\) ≤ "S"\(m\)$)#" by induction on "#fact($n ≤ m$)#" "#name("H", target: "statement:H")#" ("#cited("le", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le")#", "#cited("le_ind", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le_ind")#"):"], ()),
  step("2", [#"Case 1 (base): we prove "#claim($"S"\(n\) ≤ "S"\(n\)$)#"."], (
    step("2.1", [#"By definition of "#cited("le", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le")#" ("#cited("le_n", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le_n")#"), we have "#claim($"S"\(n\) ≤ "S"\(n\)$)#" "#by("Corelib.Init.Peano.le_n", url: "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le_n")#"."], ()),
  )),
  step("3", [#"Case 2 (inductive): we prove "#claim($∀ m_(0) ∈ ℕ , n ≤ m_(0) → "S"\(n\) ≤ "S"\(m_(0)\) → "S"\(n\) ≤ "S"\("S"\(m_(0)\)\)$)#"."], (
    step("3.1", [#"Let us choose arbitrarily "#var($m_(0) ∈ ℕ$)#"; assume "#hyp($n ≤ m_(0)$)#" "#name("H0", label: "3.1:H0")#" and by induction hypothesis "#hyp($"S"\(n\) ≤ "S"\(m_(0)\)$)#" "#name("IH", label: "3.1:IH")#"."], (
      step("3.1.1", [#"By definition of "#cited("le", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le")#" ("#cited("le_S", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le_S")#") with witness "#fact($"S"\(m_(0)\)$)#", from "#fact($"S"\(n\) ≤ "S"\(m_(0)\)$)#" "#name("IH", target: "3.1:IH")#" we deduce "#claim($"S"\(n\) ≤ "S"\("S"\(m_(0)\)\)$)#" "#by("Corelib.Init.Peano.le_S", url: "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le_S")#"."], ()),
    )),
  )),
  step("4", [#"We have "#claim($"S"\(n\) ≤ "S"\(m\)$)#" in all cases."], ()),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"),))
