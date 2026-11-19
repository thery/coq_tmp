// The proof text le_n_S', written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("le_n_S'", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($n , m ∈ ℕ$)#". Assume "#hyp($n ≤ m$)#" "#name("H", label: "statement:H")#". We prove "#claim($"S"\(n\) ≤ "S"\(m\)$)#"."], (
  steps((
    step("1", [#"We prove "#formula($"S"\(n\) ≤ "S"\(m\)$)#" by induction on "#just("H", target: "statement:H")#" ("#just("le", url: "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le")#", "#just("induction")#"):"], (
      steps((
        step("1.1", [#"Case 1 (base): we prove "#claim($"S"\(n\) ≤ "S"\(n\)$)#"."], (
          steps((
            step("1.1.1", [#"By definition of "#cited("le", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le")#" ("#just("le_n", url: "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le_n")#"), we have "#claim($"S"\(n\) ≤ "S"\(n\)$)#"."], ()),
          )),
        )),
        step("1.2", [#"Case 2 (inductive): we prove "#claim($∀ m_(0) ∈ ℕ , n ≤ m_(0) → "S"\(n\) ≤ "S"\(m_(0)\) → "S"\(n\) ≤ "S"\("S"\(m_(0)\)\)$)#"."], (
          steps((
            step("1.2.1", [#"Let us choose arbitrarily "#var($m_(0) ∈ ℕ$)#"; assume "#hyp($n ≤ m_(0)$)#" "#name("H0", label: "1.2.1:H0")#" and by induction hypothesis "#hyp($"S"\(n\) ≤ "S"\(m_(0)\)$)#" "#name("IH", label: "1.2.1:IH")#". By definition of "#cited("le", "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le")#" ("#just("le_S", url: "https://rocq-prover.org/corelib/Corelib.Init.Peano.html#le_S")#") with witness "#formula($"S"\(m_(0)\)$)#", from "#just("IH", target: "1.2.1:IH")#" we deduce "#claim($"S"\(n\) ≤ "S"\("S"\(m_(0)\)\)$)#"."], ()),
          )),
        )),
      )),
      paragraph[#"We have "#claim($"S"\(n\) ≤ "S"\(m\)$)#" in all cases."],
    )),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),))
