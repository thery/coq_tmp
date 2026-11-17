From Stdlib Require Import Reals Lra.
From Flocq Require Import Core BinarySingleNaN.
From Interval Require Import Tactic.
From Exp Require Import Common Algorithm Rnd.
From CypExp Require Import float_lemmas.
From CypV Require Import CypFile.
From CypExp Extra Dependency "float.elpi" as float_rules.
From CypExp Extra Dependency "lemma1.elpi" as lemma1_rules.
Elpi Accumulate cyp.db File float_rules.
Elpi Accumulate cyp.db File lemma1_rules.
Open Scope R_scope.
Elpi CypFile "../exp/lemma1.md".
Print Assumptions lemma1.
