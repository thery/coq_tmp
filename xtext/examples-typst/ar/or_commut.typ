// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "ar", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "ar"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"لتكن "#var($A , B : "Prop"$)#". لنفرض أن "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#". سنثبت أن "#claim($B ∨ A$)#"."], (
  steps((
    step("1", [#"سنثبت أن "#formula($B ∨ A$)#" بدراسة الحالات على "#just("h", target: "statement:h")#" ("#just("or", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#just("match")#"):"], (
      steps((
        step("1.1", [#"الحالة 1: سنثبت أن "#claim($A → B ∨ A$)#"."], (
          steps((
            step("1.1.1", [#"لنفرض أن "#hyp($A$)#" "#name("i", label: "1.1.1:i")#". حسب تعريف "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#just("or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), من "#just("i", target: "1.1.1:i")#" نستنتج أن "#claim($B ∨ A$)#"."], ()),
          )),
        )),
        step("1.2", [#"الحالة 2: سنثبت أن "#claim($B → B ∨ A$)#"."], (
          steps((
            step("1.2.1", [#"لنفرض أن "#hyp($B$)#" "#name("j", label: "1.2.1:j")#". حسب تعريف "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#just("or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), من "#just("j", target: "1.2.1:j")#" نستنتج أن "#claim($B ∨ A$)#"."], ()),
          )),
        )),
      )),
      paragraph[#"لدينا "#claim($B ∨ A$)#" في جميع الحالات."],
    )),
  )),
))

#legend((("var", "متغير"), ("hyp", "فرضية"), ("claim", "ادعاء"), ("fact", "حقيقة"), ("just", "تبرير"),))
