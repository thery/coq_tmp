// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "ko", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "ko"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#var("A B : Prop")#" 라 하자. "#hyp("A \\/ B")#" "#name("h")#" 라고 가정하자. "#claim("B \\/ A")#" 임을 보이자."]

#steps((
  step("1", [#fact("B \\/ A")#" 임을 보이자 "#fact("A \\/ B")#" "#name("h")#" (or, or_ind) 에 대한 경우 분석으로:"], ()),
  step("2", [#"경우 1: "#claim("A -> B \\/ A")#" 임을 보이자."], (
    step("2.1", [#hyp("A")#" "#name("i")#" 라고 가정하자."], (
      step("2.1.1", [#"or (or_intror) 의 정의에 의해, "#fact("A")#" "#name("i")#" 로부터 따라서 "#claim("B \\/ A")#" "#by("Corelib.Init.Logic.or_intror")#"."], ()),
    )),
  )),
  step("3", [#"경우 2: "#claim("B -> B \\/ A")#" 임을 보이자."], (
    step("3.1", [#hyp("B")#" "#name("j")#" 라고 가정하자."], (
      step("3.1.1", [#"or (or_introl) 의 정의에 의해, "#fact("B")#" "#name("j")#" 로부터 따라서 "#claim("B \\/ A")#" "#by("Corelib.Init.Logic.or_introl")#"."], ()),
    )),
  )),
  step("4", [#claim("B \\/ A")#" 모든 경우에 이다."], ()),
))
