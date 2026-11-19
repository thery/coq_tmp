// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($A , B : "Prop"$)#". Assume "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#". We prove "#claim($B ∨ A$)#"."], (
  steps((
    step("1", [#"We prove "#formula($B ∨ A$)#" by case analysis on "#just("h", target: "statement:h")#" ("#just("or", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#just("match")#"):"], (
      steps((
        step("1.1", [#"Case 1: we prove "#claim($A → B ∨ A$)#"."], (
          steps((
            step("1.1.1", [#"Assume "#hyp($A$)#" "#name("i", label: "1.1.1:i")#". By definition of "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#just("or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), from "#just("i", target: "1.1.1:i")#" we deduce "#claim($B ∨ A$)#"."], ()),
          )),
        )),
        step("1.2", [#"Case 2: we prove "#claim($B → B ∨ A$)#"."], (
          steps((
            step("1.2.1", [#"Assume "#hyp($B$)#" "#name("j", label: "1.2.1:j")#". By definition of "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#just("or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), from "#just("j", target: "1.2.1:j")#" we deduce "#claim($B ∨ A$)#"."], ()),
          )),
        )),
      )),
      paragraph[#"We have "#claim($B ∨ A$)#" in all cases."],
    )),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),))
