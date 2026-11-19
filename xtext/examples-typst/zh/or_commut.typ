// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "zh", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "zh"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"设 "#var($A , B : "Prop"$)#". 假设 "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#". 我们证明 "#claim($B ∨ A$)#"."], (
  steps((
    step("1", [#"我们证明 "#fact($B ∨ A$)#" 分情形讨论，对 "#fact($A ∨ B$)#" "#name("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#cited("or_ind", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#"):"], ()),
    step("2", [#"情形 1: 我们证明 "#claim($A → B ∨ A$)#"."], (
      steps((
        step("2.1", [#"假设 "#hyp($A$)#" "#name("i", label: "2.1:i")#"."], (
          steps((
            step("2.1.1", [#"根据定义 "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_intror", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), 由 "#fact($A$)#" "#name("i", target: "2.1:i")#" 由此可得 "#claim($B ∨ A$)#" "#emph("by")#" "#just("Corelib.Init.Logic.or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"."], ()),
          )),
        )),
      )),
    )),
    step("3", [#"情形 2: 我们证明 "#claim($B → B ∨ A$)#"."], (
      steps((
        step("3.1", [#"假设 "#hyp($B$)#" "#name("j", label: "3.1:j")#"."], (
          steps((
            step("3.1.1", [#"根据定义 "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_introl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), 由 "#fact($B$)#" "#name("j", target: "3.1:j")#" 由此可得 "#claim($B ∨ A$)#" "#emph("by")#" "#just("Corelib.Init.Logic.or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"."], ()),
          )),
        )),
      )),
    )),
    step("4", [#"我们有 "#claim($B ∨ A$)#" 在所有情形下."], ()),
  )),
))

#legend((("var", "变量"), ("hyp", "假设"), ("claim", "断言"), ("fact", "事实"), ("just", "依据"),))
