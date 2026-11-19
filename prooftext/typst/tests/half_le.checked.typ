// The proof text half_le, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: true)

#title-block("half_le", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($n ∈ ℕ$)#". We prove "#claim($n class("binary", "div") 2 ≤ n$)#"."], (
  steps((
    step("1", [#"By definition of "#cited("nat", "https://rocq-prover.org/corelib/Corelib.Init.Datatypes.html#nat")#" ("#just("strong_induction")#") on "#formula($n$)#", we prove "#claim($n class("binary", "div") 2 ≤ n$)#":"], (
      steps((
        step("1.1", [#"Let us choose arbitrarily "#var($n_(0) ∈ ℕ$)#"; assume by induction hypothesis "#hyp($∀ m ∈ ℕ , m < n_(0) → m class("binary", "div") 2 ≤ m$)#" "#name("IH", label: "1.1:IH")#"."], (
          steps((
            step("1.1.1", [#"The element "#formula($2$)#" belongs to "#formula($ℕ$)#"."], (), status: "none"),
            step("1.1.2", [#"Applying "#just("ZifyClasses.rew_iff_rev", url: "https://rocq-prover.org/stdlib/Stdlib.micromega.ZifyClasses.html#rew_iff_rev")#", we have "#claim($n_(0) ≤ 2 ⋅ n_(0)$)#"."], (
              steps((
                step("1.1.2.1", [#"The element "#formula($n_(0) ≤ 2 ⋅ n_(0)$)#" belongs to "#formula($"Prop"$)#"."], (), status: "none"),
                step("1.1.2.2", [#"The element "#formula($n_(0) ≤ "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#" belongs to "#formula($"Prop"$)#"."], (), status: "none"),
                step("1.1.2.3", [#"Applying "#just("ZifyClasses.mkrel", url: "https://rocq-prover.org/stdlib/Stdlib.micromega.ZifyClasses.html#mkrel")#", we have "#claim($n_(0) ≤ 2 ⋅ n_(0) ↔ n_(0) ≤ "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#"."], (
                  steps((
                    step("1.1.2.3.1", [#"The element "#formula($ℕ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                    step("1.1.2.3.2", [#"The element "#formula($ℤ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                    step("1.1.2.3.3", [#"The element "#formula($"le"$)#" belongs to "#formula($ℕ → ℕ → "Prop"$)#"."], (), status: "none"),
                    step("1.1.2.3.4", [#"The element "#formula($"of_nat"$)#" belongs to "#formula($ℕ → ℤ$)#"."], (), status: "none"),
                    step("1.1.2.3.5", [#"The element "#formula($"le"$)#" belongs to "#formula($ℤ → ℤ → "Prop"$)#"."], (), status: "none"),
                    step("1.1.2.3.6", [#"By "#just("Znat.Nat2Z.inj_le", url: "https://rocq-prover.org/stdlib/Stdlib.ZArith.Znat.html#Nat2Z.inj_le")#" we have "#claim($∀ n_(00) , m ∈ ℕ , n_(00) ≤ m ↔ n_(00) ≤ m$)#"."], (), status: "ok"),
                    step("1.1.2.3.7", [#"The element "#formula($n_(0)$)#" belongs to "#formula($ℤ$)#"."], (), status: "none"),
                    step("1.1.2.3.8", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#just("eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($n_(0) = n_(0)$)#"."], (), status: "ok"),
                    step("1.1.2.3.9", [#"The element "#formula($2 ⋅ n_(0)$)#" belongs to "#formula($ℕ$)#"."], (), status: "none"),
                    step("1.1.2.3.10", [#"The element "#formula($"Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#" belongs to "#formula($ℤ$)#"."], (), status: "none"),
                    step("1.1.2.3.11", [#"Applying "#just("ZifyClasses.mkapp2", url: "https://rocq-prover.org/stdlib/Stdlib.micromega.ZifyClasses.html#mkapp2")#", we have "#claim($2 ⋅ n_(0) = "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#"."], (
                      steps((
                        step("1.1.2.3.11.1", [#"The element "#formula($ℕ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                        step("1.1.2.3.11.2", [#"The element "#formula($ℕ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                        step("1.1.2.3.11.3", [#"The element "#formula($ℕ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                        step("1.1.2.3.11.4", [#"The element "#formula($ℤ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                        step("1.1.2.3.11.5", [#"The element "#formula($ℤ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                        step("1.1.2.3.11.6", [#"The element "#formula($ℤ$)#" belongs to "#formula($"Type"$)#"."], (), status: "none"),
                        step("1.1.2.3.11.7", [#"The element "#formula($"mul"$)#" belongs to "#formula($ℕ → ℕ → ℕ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.8", [#"The element "#formula($"of_nat"$)#" belongs to "#formula($ℕ → ℤ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.9", [#"The element "#formula($"of_nat"$)#" belongs to "#formula($ℕ → ℤ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.10", [#"The element "#formula($"of_nat"$)#" belongs to "#formula($ℕ → ℤ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.11", [#"The element "#formula($"mul"$)#" belongs to "#formula($ℤ → ℤ → ℤ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.12", [#"By "#just("Znat.Nat2Z.inj_mul", url: "https://rocq-prover.org/stdlib/Stdlib.ZArith.Znat.html#Nat2Z.inj_mul")#" we have "#claim($∀ n_(00) , m ∈ ℕ , n_(00) ⋅ m = n_(00) ⋅ m$)#"."], (), status: "ok"),
                        step("1.1.2.3.11.13", [#"The element "#formula($2$)#" belongs to "#formula($ℕ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.14", [#"The element "#formula($"Zpos"\("xO"\("xH"\)\)$)#" belongs to "#formula($ℤ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.15", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#just("eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($"Zpos"\("xO"\("xH"\)\) = "Zpos"\("xO"\("xH"\)\)$)#"."], (), status: "ok"),
                        step("1.1.2.3.11.16", [#"The element "#formula($n_(0)$)#" belongs to "#formula($ℤ$)#"."], (), status: "none"),
                        step("1.1.2.3.11.17", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#just("eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($n_(0) = n_(0)$)#"."], (), status: "ok"),
                      )),
                    ), status: "ok"),
                  )),
                ), status: "ok"),
                step("1.1.2.4", [#"Applying "#just("__arith")#", we have "#claim($n_(0) ≤ "Zpos"\("xO"\("xH"\)\) ⋅ n_(0)$)#"."], (
                  steps((
                    step("1.1.2.4.1", [#"Applying "#just("Znat.Nat2Z.is_nonneg", url: "https://rocq-prover.org/stdlib/Stdlib.ZArith.Znat.html#Nat2Z.is_nonneg")#" to n0, we have "#claim($"Z0" ≤ n_(0)$)#" "#name("cstr", label: "1.1.2.4.1:cstr")#"."], (), status: "ok"),
                    step("1.1.2.4.2", [#"We have proved "#claim($∀ italic("__x10") ∈ ℤ , "eval_bf"\("Zeval_formula"\("find"\("Z0", "Elt"\(italic("__x10")\)\)\), "IMPL"\("A"\("isProp", "Build_Formula"\("PEc"\("Z0"\), "OpLe", "PEX"\("xH"\)\), "tt"\), "None", "A"\("isProp", "Build_Formula"\("PEX"\("xH"\), "OpLe", "PEmul"\("PEc"\("Zpos"\("xO"\("xH"\)\)\), "PEX"\("xH"\)\)\), "tt"\)\)\)$)#" "#name("__arith", label: "1.1.2.4.2:__arith")#"."], (
                      steps((
                        step("1.1.2.4.2.1", [#"Let us choose arbitrarily "#var($italic("__x1") ∈ ℤ$)#". Let "#var($italic("__wit") ≔ "[]"$)#". Let "#var($italic("__varmap") ≔ "Elt"\(italic("__x1")\)$)#". Let "#var($italic("__ff") ≔ "IMPL"\("A"\("isProp", "Build_Formula"\("PEc"\("Z0"\), "OpLe", "PEX"\("xH"\)\), "tt"\), "None", "A"\("isProp", "Build_Formula"\("PEX"\("xH"\), "OpLe", "PEmul"\("PEc"\("Zpos"\("xO"\("xH"\)\)\), "PEX"\("xH"\)\)\), "tt"\)\)$)#"."], (
                          message("ko", "not proved: Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff"),
                          steps((
                            step("1.1.2.4.2.1.1", [#"By definition of "#cited("eq", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq")#" ("#just("eq_refl", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#eq_refl")#"), we have "#claim($"true" = "true"$)#"."], (), status: "ok"),
                            step("1.1.2.4.2.1.2", [#"The element "#formula($"find"\("Z0", italic("__varmap")\)$)#" belongs to "#formula($"PolEnv"\(ℤ\)$)#"."], (), status: "none"),
                          )),
                          paragraph[#"Applying "#just("ZMicromega.ZTautoChecker_sound", url: "https://rocq-prover.org/stdlib/Stdlib.micromega.ZMicromega.html#ZTautoChecker_sound")#", we have "#claim($"eval_bf"\("Zeval_formula"\("find"\("Z0", italic("__varmap")\)\), italic("__ff")\)$)#"."],
                        ), status: "ko"),
                      )),
                    ), status: "ok"),
                    step("1.1.2.4.3", [#"The element "#formula($n_(0)$)#" belongs to "#formula($ℤ$)#"."], (), status: "none"),
                    step("1.1.2.4.4", [#"By "#just("cstr", target: "1.1.2.4.1:cstr")#" we have "#claim($"Z0" ≤ n_(0)$)#"."], (), status: "ok"),
                  )),
                ), status: "ok"),
              )),
            ), status: "ok"),
          )),
          paragraph[#"Applying "#just("PeanoNat.Nat.Div0.div_le_upper_bound", url: "https://rocq-prover.org/stdlib/Stdlib.Arith.PeanoNat.html#Nat.Div0.div_le_upper_bound")#", we have "#claim($n_(0) class("binary", "div") 2 ≤ n_(0)$)#"."],
        ), status: "ok"),
      )),
    ), status: "ok"),
  )),
), status: "ok")

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),), statuses: (("ok", "proved"), ("ko", "not proved"), ("todo", "left to a Proof block"), ("none", "nothing to check"),))
