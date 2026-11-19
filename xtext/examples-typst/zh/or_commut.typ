// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "zh", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "zh"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"设 "#var($A , B : "Prop"$)#". 假设 "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#". 我们证明 "#claim($B ∨ A$)#"."]

#steps((
  step("1", [#"我们证明 "#formula($B ∨ A$)#" 分情形讨论，对 "#by("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#by("or_ind", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#"): 我们有 "#claim($B ∨ A$)#" 在所有情形下."], (
    step("1.1", [#"情形 1: 我们证明 "#claim($A → B ∨ A$)#"."], (
      step("1.1.1", [#"假设 "#hyp($A$)#" "#name("i", label: "1.1.1:i")#". 根据定义 "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#by("or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), 由 "#by("i", target: "1.1.1:i")#" 由此可得 "#claim($B ∨ A$)#"."], ()),
    )),
    step("1.2", [#"情形 2: 我们证明 "#claim($B → B ∨ A$)#"."], (
      step("1.2.1", [#"假设 "#hyp($B$)#" "#name("j", label: "1.2.1:j")#". 根据定义 "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#by("or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), 由 "#by("j", target: "1.2.1:j")#" 由此可得 "#claim($B ∨ A$)#"."], ()),
    )),
  )),
))

#legend((("var", "变量"), ("hyp", "假设"), ("claim", "断言"), ("fact", "事实"), ("by", "依据"),))
