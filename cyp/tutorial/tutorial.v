(* ================================================================== *)
(*  cyp tutorial, in one Rocq file                                     *)
(* ================================================================== *)

(* This file follows the tutorial cyp/TUTORIAL.md and cyp/TUTORIAL-2.md
   (https://github.com/thery/coq_tmp), section by section.  Step through
   it (Alt+↓ in rocq-web, or your editor's "next command") and read what
   Rocq prints after each command.

   cyp checks a proof written as text.  In a Markdown file, a proof looks
   like this (the tags in braces say what each formula is):

     # double_gt

     Let `n : nat`{.var}. Assume `0 < n`{.hyp} (h). We prove `n < 2 * n`{.claim}.

     - We have `n + 0 < n + n`{.claim}.
     - This is `n < 2 * n`{.claim}, since `2 * n` is `n + n`.

   and the program cyp, or the command CypFile "proof.md", checks it.
   This file uses the same proofs written as Rocq commands, Cyp Lemma, so
   that everything is in one file.  Each Cyp Lemma below has its Markdown
   form in a comment just before it.

   What Rocq prints for a Cyp Lemma:
     ✅ 1          step 1 is proved (0 is the statement itself);
     ❌ 2 reason   step 2 has an error;
     🔶 condition 3: F   step 3 is not proved by cyp: it is left as the
                   goal ?c3 of the Proof block that follows the command;
     cyp: name proved    every step is proved, and the lemma is defined.
   The steps are numbered 1, 2, ... and 2.1 for the first sub-step of 2. *)

From Stdlib Require Import Arith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope pstring_scope.

(* ------------------------------------------------------------------ *)
(* 1. The idea                                                         *)
(* ------------------------------------------------------------------ *)

(* A proof is a text.  Some formulas are coloured: a tag says what each
   one is.  cyp reads only the coloured parts; every other word is for
   the human reader.  Each step becomes a Rocq goal (a condition), which
   cyp tries to prove.  The idea comes from "Colouring proofs: a
   lightweight approach to adding formal structure to proofs" (UITP
   2003). *)

(* ------------------------------------------------------------------ *)
(* 2. A first proof                                                    *)
(* ------------------------------------------------------------------ *)

(* Cyp Lemma name binders : statement := [ step ; step ; ... ].

   The binders and the statement are those of an ordinary Lemma: they
   are the variables, hypotheses and claim of the text's first line.
   Each step is a list of strings (words) and Rocq terms (formulas).  The
   string right after a formula starts with its class: "{.claim}" for the
   claim of the step.  A string may also hold formulas written as in
   Markdown, between backquotes with their tag: "`0 < a`{.hyp} (ha)".

   The text, in Markdown:

     # sqrt_le

     Let `a b : nat`{.var}. Assume `a <= b`{.hyp} (h). We prove `Nat.sqrt a <= b /\ (0 < a -> 0 < b)`{.claim}.

     - We have `Nat.sqrt a <= a`{.claim}.
     - Assume `0 < a`{.hyp} (ha). Then `0 < b`{.claim}.
     - Hence `Nat.sqrt a <= b /\ (0 < a -> 0 < b)`{.claim}.

   It says what each step claims, never how it is proved: there is no
   justification yet.

   2.1 The conditions.  Each step gives one condition, a Rocq goal: the
   step's claim, below
   - the variables and hypotheses in scope: those of the statement, and
     the step's own (ha for step 2);
   - the claims of the steps before it, as hypotheses c1, c2, ...;  a
     step with a hypothesis is seen from the steps after it as an
     implication: step 2 is c2 : 0 < a -> 0 < b.
   The statement gives the last condition, 0: its claim, from the claims
   of its steps.

   With #[bare], cyp tries nothing: each condition is a goal of the
   Proof block, named after its step.  Step to each Show and read the
   goal:
   - c1: from h, prove Nat.sqrt a <= a;
   - c2: ha is there (the step's own hypothesis), and c1 (step 1 is
     before step 2);
   - c3: ha is gone (it holds only inside step 2), and step 2 is
     c2 : 0 < a -> 0 < b;
   - c0: the statement, from c1, c2, c3.
   They are ordinary Rocq goals: we prove them by hand.  The program cyp
   prints the same conditions for a Markdown text with
   "cyp --conditions proof.md". *)
#[bare]
Cyp Lemma sqrt_le_bare (a b : nat) (h : a <= b) : Nat.sqrt a <= b /\ (0 < a -> 0 < b) :=
  [ "We have" (Nat.sqrt a <= a) "{.claim}." ;
    "Assume `0 < a`{.hyp} (ha). Then" (0 < b) "{.claim}." ;
    "Hence" (Nat.sqrt a <= b /\ (0 < a -> 0 < b)) "{.claim}." ].
Proof.
  Show c1.
  Show c2.
  Show c3.
  Show c0.
  [c1]: apply Nat.sqrt_le_lin.
  [c2]: lia.
  [c3]: split; [lia | exact c2].
  [c0]: exact c3.
CypQed.

(* 2.2 What cyp proves by itself.  Without #[bare], cyp tries to prove
   each condition itself: with its rules, then its default tactics
   (tauto, lia, nia, lra; in Markdown, first those of the header's "by:"
   line), and a last short search.  Look at: ✅ 0, ✅ 2, ✅ 3, and
   "🔶 condition 1": lia knows nothing of Nat.sqrt, so the same goal ?c1
   is left to the Proof block. *)
Cyp Lemma sqrt_le (a b : nat) (h : a <= b) : Nat.sqrt a <= b /\ (0 < a -> 0 < b) :=
  [ "We have" (Nat.sqrt a <= a) "{.claim}." ;
    "Assume `0 < a`{.hyp} (ha). Then" (0 < b) "{.claim}." ;
    "Hence" (Nat.sqrt a <= b /\ (0 < a -> 0 < b)) "{.claim}." ].
Proof.
  Show.
  [c1]: apply Nat.sqrt_le_lin.
CypQed.

(* 2.3 Telling cyp how: justifications.  *X*{.just} says how to prove a
   step's condition: a lemma, a hypothesis, an earlier step, or a declared
   word such as a tactic (sections 3 and 6).  Step 1 now names the lemma
   that proves it.  Markdown:

     - By the lemma *Nat.sqrt_le_lin*{.just}, we have `Nat.sqrt a <= a`{.claim}.

   The condition of step 1 is the same goal; cyp hands the lemma to its
   tactics and closes it: ✅ 1, every step is proved, and the lemma is
   defined with no Proof block.  This is the whole method: the text gives
   the conditions, cyp proves what it can, justifications help it where
   it cannot, and what is left is yours, in the Proof block. *)
Cyp Lemma sqrt_le_just (a b : nat) (h : a <= b) : Nat.sqrt a <= b /\ (0 < a -> 0 < b) :=
  [ "By the lemma *Nat.sqrt_le_lin*{.just}, we have" (Nat.sqrt a <= a) "{.claim}." ;
    "Assume `0 < a`{.hyp} (ha). Then" (0 < b) "{.claim}." ;
    "Hence" (Nat.sqrt a <= b /\ (0 < a -> 0 < b)) "{.claim}." ].
Proof. CypQed.
Check sqrt_le_just.

(* A formula written as a Rocq term, (0 < b), is checked by Rocq when the
   command is read, so it may only use the names of the statement; a
   formula in a string is read by cyp in the context of its step, so it
   may use the names that the text introduces (section 3, case
   analysis).  A formula with no tag, in a string or as a term, is plain
   text: cyp does not use it. *)

(* ------------------------------------------------------------------ *)
(* 3. The roles                                                        *)
(* ------------------------------------------------------------------ *)

(* Variables, hypotheses, claims, remarks.  Markdown:

     Let `a b : nat`{.var}. Assume `a <= b`{.hyp} (hab) and `b <= 10`{.hyp} (hb). We prove `a + b <= 20`{.claim}.

     - This line is a remark: it has no tag, so cyp shows it and checks nothing.
     - By *hab*{.just} and *hb*{.just} we have `a <= 10`{.claim} (ha).
     - Let `s := a + b`{.var}. From `a <= 10`{.fact} we get `s <= 20`{.claim}.
     - Hence `a + b <= 20`{.claim}.

   - `a b : nat`{.var}: variables; `s := a + b`{.var}: a local definition;
   - `a <= b`{.hyp} (hab): a hypothesis named hab (a hypothesis with no
     name is called H1, H2, ...);
   - `a <= 10`{.claim} (ha): the conclusion of the step, named ha, so
     that later steps can refer to it; a step has exactly one;
   - a step with no tag at all is a remark: it is not checked (look:
     step 1, the remark, has no ✅ below). *)
Cyp Lemma roles (a b : nat) (hab : a <= b) (hb : b <= 10) : a + b <= 20 :=
  [ "This line is a remark: it has no tag, so cyp shows it and checks nothing." ;
    "By *hab*{.just} and *hb*{.just} we have" (a <= 10) "{.claim} (ha)." ;
    "Let `s := a + b`{.var}. From" (a <= 10) "{.fact} we get `s <= 20`{.claim}." ;
    "Hence" (a + b <= 20) "{.claim}." ].
Proof. CypQed.

(* Claim or fact?  A claim is proved here: it is the conclusion of the
   step.  A fact is used here: it must already be known, a hypothesis or
   the claim of a step that this step can see.  cyp does not prove a
   fact; it checks that it is known, and puts it first.  Markdown:

     Let `n : nat`{.var}. Assume `n <= 3`{.hyp} (h). We prove `n <= 5`{.claim}.

     - From the hypothesis `n <= 3`{.fact} we get `n <= 4`{.claim}.
     - From the step before, `n <= 4`{.fact}, we get `n <= 6`{.claim}.
     - We claim `n <= 2`{.claim}, which does not hold.
     - From `n <= 2`{.fact} we get `n <= 7`{.claim}.
     - From `n <= 1`{.fact} we get `n <= 8`{.claim}.
     - Hence `n <= 5`{.claim}.

   Look at:
   - step 3 is false: "🔶 condition 3: n <= 2", left as the goal ?c3;
   - step 4 uses the claim of step 3 as a fact, and is ✅: a fact only
     has to be known, and the claim of step 3 is known to the steps after
     it, proved or not, as on paper.  What is proved is "if step 3 holds,
     then step 4 holds".  So when a step fails, look at it first;
   - step 5 uses a fact that nothing gives: "❌ 5 the fact n <= 1 is no
     hypothesis or conclusion visible here".  Its claim, n <= 8, is the
     goal ?c5.

   Cyp Lemma never fails on a wrong step: what cyp cannot prove is left as
   goals of the Proof block, named after the steps.  Show lists them.
   ?c5 is true and lia proves it; ?c3 is false, so the proof is
   abandoned (Abort) and the lemma is not defined. *)
Cyp Lemma facts (n : nat) (h : n <= 3) : n <= 5 :=
  [ "From the hypothesis" (n <= 3) "{.fact} we get" (n <= 4) "{.claim}." ;
    "From the step before," (n <= 4) "{.fact}, we get" (n <= 6) "{.claim}." ;
    "We claim" (n <= 2) "{.claim}, which does not hold." ;
    "From" (n <= 2) "{.fact} we get" (n <= 7) "{.claim}." ;
    "From" (n <= 1) "{.fact} we get" (n <= 8) "{.claim}." ;
    "Hence" (n <= 5) "{.claim}." ].
Proof.
  Show.
  [c5]: lia.
  Fail lia.
Abort.

(* Justifications.  *X*{.just} names what a step uses: a hypothesis,
   *hp*{.just}; an earlier step, *c1*{.just} for step 1, or the name the
   text gives it, *pn*{.just}; a lemma, *Nat.add_0_r*{.just}; or a word
   such as a tactic, *lia*{.just}.
   A step may have several.  Markdown:

     - By *hp*{.just} we have `n <= n -> P n`{.claim}.
     - So, by the step before, *c1*{.just}, `P n`{.claim} (pn).
     - ... *)
Cyp Lemma justifications (P Q : nat -> Prop) (n : nat)
    (hp : forall m, m <= n -> P m) (hq : forall m, P m -> Q m) :
    Q (n + 0) /\ n * 1 = n :=
  [ "By *hp*{.just} we have" (n <= n -> P n) "{.claim}." ;
    "So, by the step before, *c1*{.just}," (P n) "{.claim} (pn)." ;
    "Applying *hq*{.just} to *pn*{.just}, we have" (Q n) "{.claim} (qn)." ;
    "By the lemma *Nat.add_0_r*{.just}," (n + 0 = n) "{.claim} (e)." ;
    "With *e*{.just} and *qn*{.just}, we get" (Q (n + 0)) "{.claim} (qn0)." ;
    "By the tactic *lia*{.just}," (n * 1 = n) "{.claim} (m1)." ;
    "By *qn0*{.just} and *m1*{.just}, we conclude" (Q (n + 0) /\ n * 1 = n) "{.claim}." ].
Proof. CypQed.

(* Case analysis.  *match*{.just} on *h*{.just} takes the hypothesis h
   apart (Rocq's destruct); *ex*{.just} says its type.  The sub-steps are
   the cases: a list [ ... ] among the parts of a step is the list of its
   sub-steps.  The case introduces a variable k and a hypothesis hk, so
   its formulas are written in strings: cyp reads them where k exists.
   The claim of the case comes after its sub-step (the closing paragraph
   of a list item, section 4).  Markdown:

     - By case analysis, *match*{.just}, on *h*{.just}, of type *ex*{.just}, we prove `exists k, n + 2 = 2 * k`{.claim}:
       - Let `k : nat`{.var} and assume `n = 2 * k`{.hyp} (hk).
         - Then `n + 2 = 2 * (k + 1)`{.claim} (e), by *hk*{.just}.

         So `exists k, n + 2 = 2 * k`{.claim}, with `k + 1` as the witness, by *ex_intro*{.just} and *e*{.just}.

   Look at the numbers: 1, 1.1, 1.1.1. *)
Cyp Lemma even_plus_two (n : nat) (h : exists k, n = 2 * k) : exists k, n + 2 = 2 * k :=
  [ "By case analysis, *match*{.just}, on *h*{.just}, of type *ex*{.just}, we prove"
      (exists k, n + 2 = 2 * k) "{.claim}:"
    [ "Let `k : nat`{.var} and assume `n = 2 * k`{.hyp} (hk)."
      [ "Then `n + 2 = 2 * (k + 1)`{.claim} (e), by *hk*{.just}." ]
      "So `exists k, n + 2 = 2 * k`{.claim}, with `k + 1` as the witness, by *ex_intro*{.just} and *e*{.just}." ] ].
Proof. CypQed.

(* Induction.  *induction*{.just} on *l*{.just}: the two sub-steps are
   the two cases, the empty list and x :: l' with the induction
   hypothesis IH, which the text states itself.  Markdown:

     - By *induction*{.just} on *l*{.just}, we prove `length (l ++ m) = length l + length m`{.claim}:
       - For the empty list, `length ([] ++ m) = length [] + length m`{.claim}, by computation, *easy*{.just}.
       - Let `x : A`{.var} and `l' : list A`{.var}; assume `length (l' ++ m) = length l' + length m`{.hyp} (IH). We prove `length ((x :: l') ++ m) = length (x :: l') + length m`{.claim}:
         - It is `S (length (l' ++ m)) = S (length l' + length m)`{.claim}, by *IH*{.just}. *)
Cyp Lemma length_app (A : Type) (l m : list A) : length (l ++ m) = length l + length m :=
  [ "By *induction*{.just} on *l*{.just}, we prove" (length (l ++ m) = length l + length m) "{.claim}:"
    [ "For the empty list," (length ([] ++ m) = length [] + length m) "{.claim}, by computation, *easy*{.just}." ;
      "Let `x : A`{.var} and `l' : list A`{.var}; assume `length (l' ++ m) = length l' + length m`{.hyp} (IH). We prove `length ((x :: l') ++ m) = length (x :: l') + length m`{.claim}:"
      [ "It is `S (length (l' ++ m)) = S (length l' + length m)`{.claim}, by *IH*{.just}." ] ] ].
Proof. CypQed.

(* Open goals.  A conclusion tagged {.goal} instead of {.claim} is a step
   the author has not proved yet: cyp does not try it, and the steps after
   it use it.  Section 8 shows one. *)

(* ------------------------------------------------------------------ *)
(* 4. Structure: steps, sub-steps, scope                               *)
(* ------------------------------------------------------------------ *)

(* - one conclusion per step;
   - the conclusion of a step follows from its sub-steps (there is no "it
     suffices to prove": going backwards is nesting);
   - the variables and hypotheses of a step hold in that step and in its
     sub-steps, nowhere else;
   - a step can use the steps before it, and those before each step
     around it;
   - seen from outside, a step with variables V, hypotheses H and
     conclusion C is the formula forall V, H -> C.

   Markdown (the claim of step 1 is in its closing paragraph, the
   paragraph after the sub-items):

     - Assume `P`{.hyp} (p).  Then:
       - By *pq*{.just} and *p*{.just}, we have `Q`{.claim} (q).
       - By *qr*{.just} and *q*{.just}, we have `R`{.claim} (r).

       So, with *r*{.just} and *q*{.just}, we have `R /\ Q`{.claim}.
     - Hence `P -> R /\ Q`{.claim}.

   With #[bare], cyp tries nothing: each step is a goal of the Proof
   block.  Look at the goals that Show prints, the conditions of the text:
   in the goal of step 2, ?c2, step 1 is the hypothesis
   c1 : P -> R /\ Q, and p, q, r are not there.  Here all of them are
   proved by tauto; without #[bare], cyp proves them itself. *)
#[bare]
Cyp Lemma structure (P Q R : Prop) (pq : P -> Q) (qr : Q -> R) : P -> R /\ Q :=
  [ "Assume `P`{.hyp} (p).  Then:"
    [ "By *pq*{.just} and *p*{.just}, we have `Q`{.claim} (q)." ;
      "By *qr*{.just} and *q*{.just}, we have `R`{.claim} (r)." ]
    "So, with *r*{.just} and *q*{.just}, we have `R /\ Q`{.claim}." ;
    "Hence" (P -> R /\ Q) "{.claim}." ].
Proof.
  Show.
  Show c2.
  all: tauto.
CypQed.

(* The program cyp prints the same conditions for a Markdown text with
   cyp --conditions proof.md, and #[bare] CypFile "proof.md" in Rocq. *)

(* ------------------------------------------------------------------ *)
(* 5. Two syntaxes: lists and prose                                    *)
(* ------------------------------------------------------------------ *)

(* In Markdown only.  A step may be a list item, as above, or written
   inside a paragraph: a span [ ... ]{.p} is a step, and the lines between
   "::: p" and ":::" are a step of several paragraphs:

     [[We have `x`{.claim}]{.p}, so by `x -> z`{.fact} we get `z`{.claim}.]{.p}

   Both give the same tree; prose keeps the paragraphs of a paper as they
   are.  Cyp Lemma has only lists.  See TUTORIAL.md, section 5. *)

(* ------------------------------------------------------------------ *)
(* 6. Justifications in depth                                          *)
(* ------------------------------------------------------------------ *)

(* A justification *X*{.just} is looked up in this order: the methods
   match and induction; a name of the text in scope (hypothesis, step,
   variable); a word declared by CypJustification; a lemma.  Anything else
   is an error of the step (section 7).

   Declaring words.  What a word means is written in the proof's files:
   - CypJustification "word" := tac.    the word runs the Ltac tactic tac;
   - CypJustification "word" := rules.  the word means the Elpi rules
     named "word", and only them.
   A rule says: on a goal of this shape, apply that lemma.  Here, on a
   goal _ * _ <= _ * _, apply Nat.mul_le_mono_r or Nat.mul_le_mono_l. *)
Ltac arith_check := lia.
CypJustification "arithmetic" := arith_check.

Elpi Accumulate cyp.db lp:{{
  named "monotonicity" {{ (_ * _ <= _ * _)%nat }} (apply {{ Nat.mul_le_mono_r }}).
  named "monotonicity" {{ (_ * _ <= _ * _)%nat }} (apply {{ Nat.mul_le_mono_l }}).
}}.
CypJustification "monotonicity" := rules.

(* Markdown (the declarations above go in a rule file named by the
   header, "rules: words.v"):

     - By *monotonicity*{.just}, `a * c <= b * c`{.claim} (s1).
     - Again by *monotonicity*{.just}, `b * c <= b * d`{.claim} (s2).
     - By *arithmetic*{.just}, `a * c <= b * d`{.claim}.
     - By *monotonicity*{.just}, `a + c <= b + d`{.claim}: no rule fits a sum.

   Look at step 4: it is true (lia proves it), but the text says it holds
   by monotonicity, and no rule of that name fits a sum.  A word declared
   as rules is the reason of the step, and nothing else is tried: Rocq
   checks the reason the text gives.  The step is left as ?c4, which the
   Proof block may still prove with a tactic. *)
Cyp Lemma words (a b c d : nat) (hab : a <= b) (hcd : c <= d) : a * c <= b * d :=
  [ "By *monotonicity*{.just}," (a * c <= b * c) "{.claim} (s1)." ;
    "Again by *monotonicity*{.just}," (b * c <= b * d) "{.claim} (s2)." ;
    "By *arithmetic*{.just}," (a * c <= b * d) "{.claim}." ;
    "By *monotonicity*{.just}," (a + c <= b + d) "{.claim}: no rule fits a sum." ].
Proof.
  Show.
  [c4]: lia.
CypQed.

(* No justification.  A step with no justification is tried with the
   rules, then the default tactics (in Markdown, those of the header's
   "by:" line; then cyp's own: tauto, lia, nia, lra), and last with the
   gap tactic, a short bounded search (case analysis on a variable,
   induction, ...).  Here step 2 needs a case analysis on o: the gap
   tactic finds it. *)
Cyp Lemma defaults (o : option nat) (n : nat) (h : n < 3) :
    option_map (fun x => x) o = o /\ n <= 2 :=
  [ "We have" (n <= 2) "{.claim}." ;
    "Whether `o` is `None` or `Some x`, the map changes nothing, so"
      (option_map (fun x => x) o = o) "{.claim}." ].
Proof. CypQed.

(* The same with #[gaps="off"] (in Markdown, the header line "gaps: off"):
   step 2 is not proved, ?c2.  A justification, *match*{.just} on
   *o*{.just}, would say how the step holds. *)
#[gaps="off"]
Cyp Lemma defaults_no_gaps (o : option nat) (n : nat) (h : n < 3) :
    option_map (fun x => x) o = o /\ n <= 2 :=
  [ "We have" (n <= 2) "{.claim}." ;
    "Whether `o` is `None` or `Some x`, the map changes nothing, so"
      (option_map (fun x => x) o = o) "{.claim}." ].
Proof.
  Show.
  [c2]: destruct o; reflexivity.
CypQed.

(* ------------------------------------------------------------------ *)
(* 7. When something is wrong                                          *)
(* ------------------------------------------------------------------ *)

(* An error never stops cyp: the step is marked ❌ with the reason, it is
   not tried, and the steps after it still use its conclusion.  One
   mistake per step:
   1 a false claim: left as ?c1;
   2 a name that names nothing: the message says how to declare a word;
   3 a fact that is not known;
   4 a step with a hypothesis and no conclusion; its sub-step 4.1 is
     checked all the same, but step 4 gives nothing to the steps after it;
   5 a name out of scope: k holds only inside step 4;
   6 two conclusions, one before and one after the sub-step: tag only one;
   7 an unknown class, {.clam}, a typo: the step has no conclusion;
   8 a formula that does not parse: Rocq's message;
   9 the statement, from the steps before it.
   The steps with a conclusion that cyp did not prove (1, 2, 3, 5) are
   goals of the Proof block; the others give no goal.  ?c1 is false, so
   the proof is abandoned. *)
Cyp Lemma errors (n : nat) (h : n <= 3) : n <= 5 :=
  [ "We have" (n <= 2) "{.claim}." ;
    "By *no_such_lemma*{.just} we have" (n <= 6) "{.claim}." ;
    "From" (n <= 1) "{.fact} we have" (n <= 7) "{.claim}." ;
    "Assume `n = 0`{.hyp} (k)."
      [ "By *k*{.just}, `n <= 1`{.claim}." ] ;
    "By *k*{.just} we have" (n <= 8) "{.claim}." ;
    "We prove" (n <= 9) "{.claim}:"
      [ "We have" (n <= 4) "{.claim}." ]
      "So" (n <= 9) "{.claim}." ;
    "We have" (n <= 10) "{.clam}." ;
    "We have `n <=`{.claim}." ;
    "Hence" (n <= 5) "{.claim}, by *h*{.just}." ].
Proof.
  Show.
Abort.

(* In Markdown, CypFile and the program cyp define the lemma only when
   every step is proved: the program exits with 0 when it is, 1 when it
   is not, 2 when it cannot run.  Cyp File and Cyp Lemma always succeed
   and leave goals; they fail only when the statement itself cannot be
   read. *)

(* ------------------------------------------------------------------ *)
(* 8. The Rocq side: the Proof block                                   *)
(* ------------------------------------------------------------------ *)

(* The goals that cyp leaves are named after their steps: ?c1 for step
   1, ?c2_1 for step 2.1.  [c1]: tac. proves one by its name, in any
   order; CypQed ends the proof.

   Here the default tactics know nothing of Nat.sqrt: step 1 is left to
   the Proof block.  Step 2 is an open goal, {.goal}: the author leaves it
   to prove, and cyp does not try it ("open goal 2 of the text").  Step 3
   uses both.  Markdown:

     - We have `Nat.sqrt a <= a`{.claim}.
     - Prove `Nat.sqrt b <= b`{.goal}.
     - Hence `Nat.sqrt a + Nat.sqrt b <= a + b`{.claim}. *)
Cyp Lemma goals (a b : nat) : Nat.sqrt a + Nat.sqrt b <= a + b :=
  [ "We have" (Nat.sqrt a <= a) "{.claim}." ;
    "Prove" (Nat.sqrt b <= b) "{.goal}." ;
    "Hence" (Nat.sqrt a + Nat.sqrt b <= a + b) "{.claim}." ].
Proof.
  Show.
  [c2]: apply Nat.sqrt_le_lin.
  [c1]: apply Nat.sqrt_le_lin.
CypQed.
Check goals.

(* For a Markdown text, the same Proof block follows Cyp File (two
   words):

     Cyp File "goals.md".
     Proof. [c2]: apply Nat.sqrt_le_lin. [c1]: apply Nat.sqrt_le_lin. CypQed.

   and cyp writes goals.checked.md, the text with a mark per step (✅ ❌ 🔶
   ▫️); prooftext/pdf.sh makes its PDF.  These need a Markdown file: see
   TUTORIAL.md, section 2, and TUTORIAL-2.md, section 8.

   With the environment variable CYP_TIME set, cyp prints the time spent
   on each condition. *)

(* ------------------------------------------------------------------ *)
(* 9. Writing a text from a Rocq proof: xtext                          *)
(* ------------------------------------------------------------------ *)

(* The other way round: ExtractText foo. prints the proof of the lemma
   foo as text, and ExtractText foo to "foo.md". writes it as a cyp text,
   formulas and justifications tagged; cyp can check it again.  See the
   example xtext of rocq-web, and TUTORIAL-2.md, section 9. *)

(* ------------------------------------------------------------------ *)
(* 10. Reference card                                                  *)
(* ------------------------------------------------------------------ *)

(* Tags:  `x y : T`{.var}  `u := e`{.var}  `A`{.hyp} (h)  `C`{.claim} (n)
          `G`{.goal}  `F`{.fact}  *X*{.just}; no tag: plain text; a step
          with no tag: a remark.
   Steps: a list item; in Markdown also [ ... ]{.p} and ::: p ... :::.
   Commands: Cyp Lemma ... := [ ... ]. Proof. ... CypQed.
             Cyp File "p.md". Proof. ... CypQed.   CypFile "p.md".
             #[bare] (try nothing)   #[gaps="off"] (no gap tactic)
             CypJustification "w" := tac.   CypJustification "w" := rules.
   The full card: TUTORIAL-2.md, section 10. *)
