// The proof text or_commut, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "ar", numbers: false)

#title-block("or_commut", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper."),
  ("lang", "ar"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"لتكن "#var($A , B : "Prop"$)#". لنفرض أن "#hyp($A ∨ B$)#" "#name("h")#". سنثبت أن "#claim($B ∨ A$)#"."]

#steps((
  step("1", [#"سنثبت أن "#fact($B ∨ A$)#" بدراسة الحالات على "#fact($A ∨ B$)#" "#name("h")#" (or, or_ind):"], ()),
  step("2", [#"الحالة 1: سنثبت أن "#claim($A → B ∨ A$)#"."], (
    step("2.1", [#"لنفرض أن "#hyp($A$)#" "#name("i")#"."], (
      step("2.1.1", [#"حسب تعريف or (or_intror), من "#fact($A$)#" "#name("i")#" نستنتج أن "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_intror")#"."], ()),
    )),
  )),
  step("3", [#"الحالة 2: سنثبت أن "#claim($B → B ∨ A$)#"."], (
    step("3.1", [#"لنفرض أن "#hyp($B$)#" "#name("j")#"."], (
      step("3.1.1", [#"حسب تعريف or (or_introl), من "#fact($B$)#" "#name("j")#" نستنتج أن "#claim($B ∨ A$)#" "#by("Corelib.Init.Logic.or_introl")#"."], ()),
    )),
  )),
  step("4", [#"لدينا "#claim($B ∨ A$)#" في جميع الحالات."], ()),
))
