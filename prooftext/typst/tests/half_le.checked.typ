// The proof text half_le, written by prooftext (write-typst).
// Its PDF: prooftext/pdf.sh, or typst compile --package-path prooftext/typst.
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: true)

#title-block("half_le", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.elim_type."),
  ("flags", "-R /home/thery/git/coq_tmp/xtext XText"),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement(status: "ok")[#"Let "#var("n : nat")#". We prove "#claim("n / 2 <= n")#"."]

#steps((
  step("1", [#"By definition of nat (strong_induction), we prove "#claim("forall n0 : nat, n0 / 2 <= n0")#":"], (
    step("1.1", [#"Let us choose arbitrarily "#var("n0 : nat")#"; assume by induction hypothesis "#hyp("forall m : nat, m < n0 -> m / 2 <= m")#" "#name("IH")#"."], (
      step("1.1.1", [#"The element "#fact("n0")#" belongs to "#fact("nat")#"."], (), status: "none"),
      step("1.1.2", [#"The element "#fact("2")#" belongs to "#fact("nat")#"."], (), status: "none"),
      step("1.1.3", [#"The element "#fact("n0")#" belongs to "#fact("nat")#"."], (), status: "none"),
      step("1.1.4", [#"Applying rew_iff_rev, we have "#claim("n0 <= 2 * n0")#"."], (
        step("1.1.4.1", [#"The element "#fact("n0 <= 2 * n0")#" belongs to "#fact("Prop")#"."], (), status: "none"),
        step("1.1.4.2", [#"The element "#fact("BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))")#" belongs to "#fact("Prop")#"."], (), status: "none"),
        step("1.1.4.3", [#"Applying mkrel, we have "#claim("n0 <= 2 * n0 <-> BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))")#"."], (
          step("1.1.4.3.1", [#"The element "#fact("nat")#" belongs to "#fact("Type")#"."], (), status: "none"),
          step("1.1.4.3.2", [#"The element "#fact("BinNums.Z")#" belongs to "#fact("Type")#"."], (), status: "none"),
          step("1.1.4.3.3", [#"The element "#fact("le")#" belongs to "#fact("nat -> nat -> Prop")#"."], (), status: "none"),
          step("1.1.4.3.4", [#"The element "#fact("BinInt.Z.of_nat")#" belongs to "#fact("nat -> BinNums.Z")#"."], (), status: "none"),
          step("1.1.4.3.5", [#"The element "#fact("BinInt.Z.le")#" belongs to "#fact("BinNums.Z -> BinNums.Z -> Prop")#"."], (), status: "none"),
          step("1.1.4.3.6", [#"By inj_le we have "#claim("forall n00 m : nat, n00 <= m <-> BinInt.Z.le (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)")#"."], (), status: "ok"),
          step("1.1.4.3.7", [#"The element "#fact("n0")#" belongs to "#fact("nat")#"."], (), status: "none"),
          step("1.1.4.3.8", [#"The element "#fact("BinInt.Z.of_nat n0")#" belongs to "#fact("BinNums.Z")#"."], (), status: "none"),
          step("1.1.4.3.9", [#"By definition of eq (eq_refl), we have "#claim("BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0")#" "#by("Corelib.Init.Logic.eq_refl")#"."], (), status: "ok"),
          step("1.1.4.3.10", [#"The element "#fact("2 * n0")#" belongs to "#fact("nat")#"."], (), status: "none"),
          step("1.1.4.3.11", [#"The element "#fact("BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)")#" belongs to "#fact("BinNums.Z")#"."], (), status: "none"),
          step("1.1.4.3.12", [#"Applying mkapp2, we have "#claim("BinInt.Z.of_nat (2 * n0) = BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0)")#"."], (
            step("1.1.4.3.12.1", [#"The element "#fact("nat")#" belongs to "#fact("Type")#"."], (), status: "none"),
            step("1.1.4.3.12.2", [#"The element "#fact("nat")#" belongs to "#fact("Type")#"."], (), status: "none"),
            step("1.1.4.3.12.3", [#"The element "#fact("nat")#" belongs to "#fact("Type")#"."], (), status: "none"),
            step("1.1.4.3.12.4", [#"The element "#fact("BinNums.Z")#" belongs to "#fact("Type")#"."], (), status: "none"),
            step("1.1.4.3.12.5", [#"The element "#fact("BinNums.Z")#" belongs to "#fact("Type")#"."], (), status: "none"),
            step("1.1.4.3.12.6", [#"The element "#fact("BinNums.Z")#" belongs to "#fact("Type")#"."], (), status: "none"),
            step("1.1.4.3.12.7", [#"The element "#fact("Nat.mul")#" belongs to "#fact("nat -> nat -> nat")#"."], (), status: "none"),
            step("1.1.4.3.12.8", [#"The element "#fact("BinInt.Z.of_nat")#" belongs to "#fact("nat -> BinNums.Z")#"."], (), status: "none"),
            step("1.1.4.3.12.9", [#"The element "#fact("BinInt.Z.of_nat")#" belongs to "#fact("nat -> BinNums.Z")#"."], (), status: "none"),
            step("1.1.4.3.12.10", [#"The element "#fact("BinInt.Z.of_nat")#" belongs to "#fact("nat -> BinNums.Z")#"."], (), status: "none"),
            step("1.1.4.3.12.11", [#"The element "#fact("BinInt.Z.mul")#" belongs to "#fact("BinNums.Z -> BinNums.Z -> BinNums.Z")#"."], (), status: "none"),
            step("1.1.4.3.12.12", [#"By inj_mul we have "#claim("forall n00 m : nat, BinInt.Z.of_nat (n00 * m) = BinInt.Z.mul (BinInt.Z.of_nat n00) (BinInt.Z.of_nat m)")#"."], (), status: "ok"),
            step("1.1.4.3.12.13", [#"The element "#fact("2")#" belongs to "#fact("nat")#"."], (), status: "none"),
            step("1.1.4.3.12.14", [#"The element "#fact("BinNums.Zpos (BinNums.xO BinNums.xH)")#" belongs to "#fact("BinNums.Z")#"."], (), status: "none"),
            step("1.1.4.3.12.15", [#"By definition of eq (eq_refl), we have "#claim("BinNums.Zpos (BinNums.xO BinNums.xH) = BinNums.Zpos (BinNums.xO BinNums.xH)")#" "#by("Corelib.Init.Logic.eq_refl")#"."], (), status: "ok"),
            step("1.1.4.3.12.16", [#"The element "#fact("n0")#" belongs to "#fact("nat")#"."], (), status: "none"),
            step("1.1.4.3.12.17", [#"The element "#fact("BinInt.Z.of_nat n0")#" belongs to "#fact("BinNums.Z")#"."], (), status: "none"),
            step("1.1.4.3.12.18", [#"By definition of eq (eq_refl), we have "#claim("BinInt.Z.of_nat n0 = BinInt.Z.of_nat n0")#" "#by("Corelib.Init.Logic.eq_refl")#"."], (), status: "ok"),
          ), status: "ok"),
        ), status: "ok"),
        step("1.1.4.4", [#"Applying __arith, we have "#claim("BinInt.Z.le (BinInt.Z.of_nat n0) (BinInt.Z.mul (BinNums.Zpos (BinNums.xO BinNums.xH)) (BinInt.Z.of_nat n0))")#"."], (
          step("1.1.4.4.1", [#"Applying is_nonneg to n0, we have "#claim("BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)")#" "#name("cstr")#"."], (), status: "ok"),
          step("1.1.4.4.2", [#"We have proved "#claim("forall __x10 : BinNums.Z, Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 (VarMap.Elt __x10))) (Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt))")#" "#name("__arith")#"."], (
            step("1.1.4.4.2.1", [#"Let us choose arbitrarily "#var("__x1 : BinNums.Z")#"."], (
              step("1.1.4.4.2.1.1", [#"Let "#var("__wit : list ZMicromega.ZArithProof := nil")#"."], (), status: "none"),
              step("1.1.4.4.2.1.2", [#"Let "#var("__varmap : VarMap.t BinNums.Z := VarMap.Elt __x1")#"."], (), status: "none"),
              step("1.1.4.4.2.1.3", [#"Let "#var("__ff : Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp := Tauto.IMPL (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEc BinNums.Z0; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEX BinNums.xH |} tt) None (Tauto.A Tauto.isProp {| RingMicromega.Flhs := EnvRing.PEX BinNums.xH; RingMicromega.Fop := RingMicromega.OpLe; RingMicromega.Frhs := EnvRing.PEmul (EnvRing.PEc (BinNums.Zpos (BinNums.xO BinNums.xH))) (EnvRing.PEX BinNums.xH) |} tt)")#"."], (), status: "none"),
              step("1.1.4.4.2.1.4", [#"The element "#fact("__ff")#" belongs to "#fact("Tauto.BFormula (RingMicromega.Formula BinNums.Z) Tauto.isProp")#"."], (), status: "none"),
              step("1.1.4.4.2.1.5", [#"The element "#fact("__wit")#" belongs to "#fact("list ZMicromega.ZArithProof")#"."], (), status: "none"),
              step("1.1.4.4.2.1.6", [#"By definition of eq (eq_refl), we have "#claim("true = true")#" "#by("Corelib.Init.Logic.eq_refl")#"."], (), status: "ok"),
              step("1.1.4.4.2.1.7", [#"The element "#fact("VarMap.find BinNums.Z0 __varmap")#" belongs to "#fact("RingMicromega.PolEnv BinNums.Z")#"."], (), status: "none"),
              step("1.1.4.4.2.1.8", [#"Applying ZTautoChecker_sound, we have "#claim("Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff")#"."], (), status: "ko", message: "not proved: Tauto.eval_bf (ZMicromega.Zeval_formula (VarMap.find BinNums.Z0 __varmap)) __ff"),
            ), status: "none"),
          ), status: "ok"),
          step("1.1.4.4.3", [#"The element "#fact("BinInt.Z.of_nat n0")#" belongs to "#fact("BinNums.Z")#"."], (), status: "none"),
          step("1.1.4.4.4", [#"By cstr we have "#claim("BinInt.Z.le BinNums.Z0 (BinInt.Z.of_nat n0)")#"."], (), status: "ok"),
        ), status: "ok"),
      ), status: "ok"),
      step("1.1.5", [#"Applying div_le_upper_bound, we have "#claim("n0 / 2 <= n0")#"."], (), status: "ko", message: "not proved: n0 / 2 <= n0"),
    ), status: "none"),
  ), status: "ko", message: "not proved: forall n0 : nat, n0 / 2 <= n0"),
  step("2", [#"In particular "#claim("n / 2 <= n")#"."], (), status: "ok"),
))
