// The proof text plus_n_Sm', written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("plus_n_Sm'", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($n , m ∈ ℕ$)#". We prove "#claim($"S"\(n + m\) = n + "S"\(m\)$)#"."], (
  steps((
    step("1", [#"We prove "#fact($"S"\(n + m\) = n + "S"\(m\)$)#" by induction on "#fact($n$)#" ("#cited("nat", "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat")#", "#cited("nat_ind", "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat_ind")#"):"], ()),
    step("2", [#"Case 1 (base): we prove "#claim($0 + "S"\(m\) = 0 + "S"\(m\)$)#"."], (
      steps((
        step("2.1", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($0 + "S"\(m\) = 0 + "S"\(m\)$)#" "#emph("by")#" "#just("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], ()),
      )),
    )),
    step("3", [#"Case 2 (inductive): we prove "#claim($∀ n_(0) ∈ ℕ , "S"\(n_(0) + m\) = n_(0) + "S"\(m\) → "S"\("S"\(n_(0)\) + m\) = "S"\(n_(0)\) + "S"\(m\)$)#"."], (
      steps((
        step("3.1", [#"Let us choose arbitrarily "#var($n_(0) ∈ ℕ$)#"; assume by induction hypothesis "#hyp($"S"\(n_(0) + m\) = n_(0) + "S"\(m\)$)#" "#name("IH", label: "3.1:IH")#"."], (
          steps((
            step("3.1.1", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#cited("eq_refl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($"S"\(n_(0) + "S"\(m\)\) = "S"\(n_(0) + "S"\(m\)\)$)#" "#emph("by")#" "#just("Corelib.Init.Logic.eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"."], ()),
            step("3.1.2", [#"By "#named("IH", "3.1:IH")#" we have "#claim($"S"\(n_(0) + m\) = n_(0) + "S"\(m\)$)#"."], ()),
            step("3.1.3", [#"Rewriting with "#fact($"S"\(n_(0) + m\) = n_(0) + "S"\(m\)$)#" from right to left ("#cited("eq_ind_r", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_ind_r")#"), we get "#claim($"S"\("S"\(n_(0) + m\)\) = "S"\(n_(0) + "S"\(m\)\)$)#"."], ()),
          )),
        )),
      )),
    )),
    step("4", [#"These cases being exhaustive, we deduce "#claim($"S"\(n + m\) = n + "S"\(m\)$)#" "#emph("by")#" "#just("Corelib.Init.Datatypes.nat_ind", url: "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat_ind")#"."], ()),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),))
