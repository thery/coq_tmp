// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "ar", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "ar"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"لتكن "#var($A , B : "Prop"$)#". لنفرض أن "#hyp($A ∨ B$)#" "#name("h", label: "statement:h")#". سنثبت أن "#claim($B ∨ A$)#"."]

#steps((
  step("1", [#"سنثبت أن "#fact($B ∨ A$)#" بدراسة الحالات على "#fact($A ∨ B$)#" "#name("h", target: "statement:h")#" ("#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#", "#cited("or_ind", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind")#"):"], ()),
  step("2", [#"الحالة 1: سنثبت أن "#claim($A → B ∨ A$)#"."], (
    step("2.1", [#"لنفرض أن "#hyp($A$)#" "#name("i", label: "2.1:i")#"."], (
      step("2.1.1", [#"حسب تعريف "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_intror", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"), من "#fact($A$)#" "#name("i", target: "2.1:i")#" نستنتج أن "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")#"."], ()),
    )),
  )),
  step("3", [#"الحالة 2: سنثبت أن "#claim($B → B ∨ A$)#"."], (
    step("3.1", [#"لنفرض أن "#hyp($B$)#" "#name("j", label: "3.1:j")#"."], (
      step("3.1.1", [#"حسب تعريف "#cited("or", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or")#" ("#cited("or_introl", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"), من "#fact($B$)#" "#name("j", target: "3.1:j")#" نستنتج أن "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_introl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_introl")#"."], ()),
    )),
  )),
  step("4", [#"لدينا "#claim($B ∨ A$)#" في جميع الحالات."], ()),
))

#legend((("var", "متغير"), ("hyp", "فرضية"), ("claim", "ادعاء"), ("fact", "حقيقة"), ("by", "تبرير"),))
