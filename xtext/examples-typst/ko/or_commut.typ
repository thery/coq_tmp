// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "ko", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "ko"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#var($A , B : "Prop"$)#" 라 하자. "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#" 라고 가정하자. "#claim($B ∨ A$)#" 임을 보이자."], (
  steps((
    step("1", [#formula($B ∨ A$)#" 임을 보이자 "#just("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#just("or_ind", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#") 에 대한 경우 분석으로:"], (
      steps((
        step("1.1", [#"경우 1: "#claim($A → B ∨ A$)#" 임을 보이자."], (
          steps((
            step("1.1.1", [#hyp($A$)#" "#name("i", label: "1.1.1:i")#" 라고 가정하자. "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#just("or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#") 의 정의에 의해, "#just("i", target: "1.1.1:i")#" 로부터 따라서 "#claim($B ∨ A$)#"."], ()),
          )),
        )),
        step("1.2", [#"경우 2: "#claim($B → B ∨ A$)#" 임을 보이자."], (
          steps((
            step("1.2.1", [#hyp($B$)#" "#name("j", label: "1.2.1:j")#" 라고 가정하자. "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#just("or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#") 의 정의에 의해, "#just("j", target: "1.2.1:j")#" 로부터 따라서 "#claim($B ∨ A$)#"."], ()),
          )),
        )),
      )),
      paragraph[#claim($B ∨ A$)#" 모든 경우에 이다."],
    )),
  )),
))

#legend((("var", "변수"), ("hyp", "가정"), ("claim", "주장"), ("fact", "사실"), ("just", "근거"),))
