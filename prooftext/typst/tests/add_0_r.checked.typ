// The proof text add_0_r', written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: true)

#title-block("add_0_r'", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($n ∈ ℕ$)#". We prove "#claim($n + 0 = n$)#"."], (
  steps((
    step("1", [#"We prove "#formula($n + 0 = n$)#" by induction on "#just("n")#" ("#just("nat", url: "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat")#", "#just("induction")#"):"], (
      steps((
        step("1.1", [#"Case 1 (base): we prove "#claim($0 = 0$)#"."], (
          steps((
            step("1.1.1", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#just("eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($0 = 0$)#"."], (), status: "ok"),
          )),
        ), status: "ok"),
        step("1.2", [#"Case 2 (inductive): we prove "#claim($∀ m ∈ ℕ , m + 0 = m → "S"\(m\) + 0 = "S"\(m\)$)#"."], (
          steps((
            step("1.2.1", [#"Let us choose arbitrarily "#var($m ∈ ℕ$)#"; assume by induction hypothesis "#hyp($m + 0 = m$)#" "#name("IH", label: "1.2.1:IH")#"."], (
              steps((
                step("1.2.1.1", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#just("eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($"S"\(m\) = "S"\(m\)$)#"."], (), status: "ok"),
                step("1.2.1.2", [#"By "#just("IH", target: "1.2.1:IH")#" we have "#claim($m + 0 = m$)#"."], (), status: "ok"),
              )),
              paragraph[#"Rewriting with "#fact($m + 0 = m$)#" from right to left ("#cited("eq_ind_r", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_ind_r")#"), we get "#claim($"S"\(m + 0\) = "S"\(m\)$)#"."],
            ), status: "ok"),
          )),
        ), status: "ok"),
      )),
      paragraph[#"These cases being exhaustive, we deduce "#claim($n + 0 = n$)#"."],
    ), status: "ok"),
  )),
), status: "ok")

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),), statuses: (("ok", "proved"), ("ko", "not proved"), ("todo", "left to a Proof block"), ("none", "nothing to check"),))
