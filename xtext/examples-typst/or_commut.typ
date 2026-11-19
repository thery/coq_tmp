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
    step("1", [#"We prove "#fact($B ∨ A$)#" by case analysis on "#fact($A ∨ B$)#" "#name("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#cited("or_ind", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#"):"], ()),
    step("2", [#"Case 1: we prove "#claim($A → B ∨ A$)#"."], (
      steps((
        step("2.1", [#"Assume "#hyp($A$)#" "#name("i", label: "2.1:i")#"."], (
          steps((
            step("2.1.1", [#"By definition of "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_intror", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), from "#fact($A$)#" "#name("i", target: "2.1:i")#" we deduce "#claim($B ∨ A$)#" "#emph("by")#" "#just("Corelib.Init.Logic.or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"."], ()),
          )),
        )),
      )),
    )),
    step("3", [#"Case 2: we prove "#claim($B → B ∨ A$)#"."], (
      steps((
        step("3.1", [#"Assume "#hyp($B$)#" "#name("j", label: "3.1:j")#"."], (
          steps((
            step("3.1.1", [#"By definition of "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_introl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), from "#fact($B$)#" "#name("j", target: "3.1:j")#" we deduce "#claim($B ∨ A$)#" "#emph("by")#" "#just("Corelib.Init.Logic.or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"."], ()),
          )),
        )),
      )),
    )),
    step("4", [#"We have "#claim($B ∨ A$)#" in all cases."], ()),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),))
