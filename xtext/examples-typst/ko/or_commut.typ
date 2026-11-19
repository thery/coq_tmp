// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "ko", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "ko"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#var($A , B : "Prop"$)#" 라 하자. "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#" 라고 가정하자. "#claim($B ∨ A$)#" 임을 보이자."]

#steps((
  step("1", [#fact($B ∨ A$)#" 임을 보이자 "#fact($A ∨ B$)#" "#name("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#cited("or_ind", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#") 에 대한 경우 분석으로:"], ()),
  step("2", [#"경우 1: "#claim($A → B ∨ A$)#" 임을 보이자."], (
    step("2.1", [#hyp($A$)#" "#name("i", label: "2.1:i")#" 라고 가정하자."], (
      step("2.1.1", [#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_intror", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#") 의 정의에 의해, "#fact($A$)#" "#name("i", target: "2.1:i")#" 로부터 따라서 "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"."], ()),
    )),
  )),
  step("3", [#"경우 2: "#claim($B → B ∨ A$)#" 임을 보이자."], (
    step("3.1", [#hyp($B$)#" "#name("j", label: "3.1:j")#" 라고 가정하자."], (
      step("3.1.1", [#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_introl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#") 의 정의에 의해, "#fact($B$)#" "#name("j", target: "3.1:j")#" 로부터 따라서 "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"."], ()),
    )),
  )),
  step("4", [#claim($B ∨ A$)#" 모든 경우에 이다."], ()),
))

#legend((("var", "변수"), ("hyp", "가정"), ("claim", "주장"), ("fact", "사실"), ("by", "근거"),))
