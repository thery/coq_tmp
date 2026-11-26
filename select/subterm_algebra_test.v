(* Tests of subterm_algebra.v: the concrete syntax, the denotation, the
   laws (normal forms), law 3 with its side condition, the translation to
   ssreflect with its round trip, the robustness.

   sel_normal_expect also checks that the normal form denotes what the
   selector denotes; sel_to_ssr_expect checks the round trip: the pattern
   it gives, read back as a selector, denotes what the selector denotes. *)

From elpi Require Import elpi.
From coq_tmp Require Import subterm_algebra.

(* ---------------- The tutorial's running example ---------------- *)

(* f (a + b) (2 * (a + c)) + (c + d) + f a (c + d) = 0; the target is the
   last c + d, at 2.2.2; the first one is at 2.1.2 *)
Goal forall (f : nat -> nat -> nat) (a b c d : nat),
  f (a + b) (2 * (a + c)) + (c + d) + f a (c + d) = 0.
intros f a b c d.

(* the syntax: paths, root, unicode *)
elpi sel_denote_expect "2;2;2" "2.2.2".
elpi sel_denote_expect "2.2.2" "2.2.2".
elpi sel_denote_expect "root" "root".
elpi sel_denote_expect "ε ; 3" "3".
elpi sel_denote_expect "2;7" "".
elpi sel_denote_expect "⟨f a X | X⟩" "2.2.2".

(* one selector of every kind: denotation and ssreflect form *)
elpi sel_denote "2;2;2".
elpi sel_to_ssr_expect "2;2;2" "{2}[c + d]".                          (* A1 *)
elpi sel_denote_expect "<c + d>" "2.1.2 2.2.2".
elpi sel_to_ssr_expect "<c + d>" "[c + d]".                           (* B1 *)
elpi sel_denote_expect "<_ + d>" "2.1.2 2.2.2".
elpi sel_to_ssr_expect "<_ + d>" "[_ + d]".                           (* B2 *)
elpi sel_denote_expect "<f a X | X>" "2.2.2".
elpi sel_to_ssr_expect "<f a X | X>" "[X in f a X]".                  (* C1 *)
elpi sel_denote_expect "<f _ X | X>" "2.1.1.2".
elpi sel_to_ssr_expect "<f _ X | X>" "[X in f _ X]".
elpi sel_denote_expect "<f a X | X> ; <_ + d>" "2.2.2".
elpi sel_to_ssr_expect "<f a X | X> ; <_ + d>" "[_ + d in X in f a X]".  (* C2 *)
elpi sel_denote_expect "<f _ X | X := _ + d>" "2.2.2".
elpi sel_to_ssr_expect "<f _ X | X := _ + d>" "[_ + d as X in f _ X]".  (* C3 *)
elpi sel_denote_expect "<_ + d> # 2" "2.2.2".
elpi sel_to_ssr_expect "<_ + d> # 2" "{2}[_ + d]".                    (* E1 *)
elpi sel_denote_expect "<_ + d> # {-1}" "2.2.2".
elpi sel_to_ssr_expect "<_ + d> # {-1}" "{-1}[_ + d]".
elpi sel_denote_expect "RHS" "3".
elpi sel_to_ssr_expect "RHS" "[X in _ = X]".                          (* E2 *)
elpi sel_denote_expect "LHS ; 2 ; 2" "2.2.2".
elpi sel_to_ssr_expect "LHS ; 2 ; 2" "{2}[c + d]".
(* an ssreflect pattern as an atom *)
elpi sel_denote_expect "[_ + d in X in f a X]" "2.2.2".
elpi sel_denote_expect "{2}[_ + d]" "2.2.2".
(* union: two different terms have no ssreflect form *)
elpi sel_denote_expect "<a + b> ++ <a + c>" "2.1.1.1 2.1.1.2.2".
elpi sel_to_ssr_expect "<a + b> ++ <a + c>" "none".
(* the union of the two copies of c + d is their occurrences *)
elpi sel_denote_expect "2;1;2 ++ 2;2;2" "2.1.2 2.2.2".
elpi sel_to_ssr_expect "2;1;2 ++ 2;2;2" "[c + d]".
(* the whole goal *)
elpi sel_to_ssr_expect "root" "[f (a + b) (2 * (a + c)) + (c + d) + f a (c + d) = 0]".
(* nothing selected; a failure *)
elpi sel_to_ssr_expect "<c + d> # 3" "none".
elpi sel_denote_expect "<f a X | X> ; <a + _>" "error".
(* it fails as the ssreflect pattern fails: the same denotation *)
elpi sel_to_ssr_expect "<f a X | X> ; <a + _>" "[a + _ in X in f a X]".

(* law 1: paths *)
elpi sel_normal_expect "root ; 2 ; (2 ; root) ; 2" "2 ; 2 ; 2".
elpi sel_normal_expect "root ; root" "root".
(* law 4: an as with a hole for redex is the plain hole; an as is one hole *)
elpi sel_normal_expect "<f a X | X := _>" "<f a X | X>".
elpi sel_normal_expect "[_ + d as X in f _ X]" "<f _ X | X := _ + d>".
(* law 5: ranks of ranks, and a pick that keeps all *)
elpi sel_normal_expect "<c + d> # {1 2} # 2" "<c + d> # 2".
elpi sel_normal_expect "<c + d> # {-1} # 1" "<c + d> # 2".
elpi sel_normal_expect "(2.1.2 ++ 2.2.2 ++ 2.1.1.1) # {-3} # {-1}" "(2 ; 1 ; 2 ++ 2 ; 2 ; 2 ++ 2 ; 1 ; 1 ; 1) # {-1 3}".
elpi sel_normal_expect "<c + d> # {2 3} # {-1}" "<c + d> # 3".
elpi sel_normal_expect "<c + d> # {1 2}" "<c + d>".
elpi sel_normal_expect "<f a X | X> # 1" "<f a X | X>".

(* law 3 where its side condition holds: the X part of the first f _ _,
   2 * (a + c), is an instance of 2 * _; the flattened context is then made
   smaller by anti-unification (checked to denote the same position) *)
elpi sel_denote_expect "<f _ X | X> ; <2 * Y | Y>" "2.1.1.2.2".
elpi sel_denote_expect "<f _ (2 * Y) | Y>" "2.1.1.2.2".
elpi sel_normal_expect "<f _ X | X> ; <2 * Y | Y>" "<f _ (2 * Y) | Y>".
elpi sel_to_ssr_expect "<f _ X | X> ; <2 * Y | Y>" "[X in f _ (_ * X)]".
(* and with a redex at Y *)
elpi sel_normal_expect "<f _ X | X> ; <2 * Y | Y := _ + c>" "<f _ (2 * Y) | Y := _ + c>".
elpi sel_to_ssr "<f _ X | X> ; <2 * Y | Y := _ + c>".
(* the side condition fails: the X part of the first f, 2 * (a + c), is not
   an instance of _ + _; not flattened *)
elpi sel_denote_expect "<f _ X | X> ; <Y + _ | Y>" "2.1.1.2.2.1".
elpi sel_normal_expect "<f _ X | X> ; <Y + _ | Y>" "<f _ X | X> ; <Y + _ | Y>".
elpi sel_denote_expect "<f _ (Y + _) | Y>" "2.2.2.1".
elpi sel_to_ssr_expect "<f _ X | X> ; <Y + _ | Y>" "{2}[a]".

(* robustness: margin against the later same-key competitors *)
elpi sel_denote "<f _ X | X>".
(* the first f _ _ matches the later f a (c + d): margin 0 *)
elpi sel_robustness_expect "<f _ X | X>" "0 2.2".
(* f a _ has no later f *)
elpi sel_robustness_expect "<f a X | X>" "none".
(* _ + d: the later + are copies of c + d *)
elpi sel_robustness_expect "<_ + d>" "none".
(* _ + _ matches all the later sums *)
elpi sel_robustness_expect "<_ + _>" "0 2.1 2.1.1.1 2.1.1.2.2 2.1.2 2.2.2".
(* a + c against c + d: both places kept; _ + c against c + d: one *)
elpi sel_robustness_expect "<a + c>" "2 2.1.2 2.2.2".
elpi sel_robustness_expect "<_ + c>" "1 2.1.2 2.2.2".
(* a pick: the left out later copy is at margin 0 *)
elpi sel_robustness_expect "<c + d> # 1" "0 2.2.2".
elpi sel_robustness_expect "<c + d> # 2" "none".
(* composition: the minimum of the parts *)
elpi sel_robustness_expect "<f _ X | X> ; <_ + c>" "0 2.2".
elpi sel_robustness_expect "<f a X | X> ; <_ + d>" "none".
(* a path has no competitor *)
elpi sel_robustness_expect "2;2;2" "none".
Abort.

(* names *)
Elpi sel_define "SNDA" "<f a X | X>".
Goal forall (f : nat -> nat -> nat) (a b c d : nat),
  f (a + b) (2 * (a + c)) + (c + d) + f a (c + d) = 0.
intros f a b c d.
elpi sel_denote_expect "SNDA" "2.2.2".
elpi sel_denote_expect "SNDA ; <_ + d>" "2.2.2".
elpi sel_to_ssr_expect "SNDA ; <_ + d>" "[_ + d in X in f a X]".
Abort.

(* ---------------- Law 3: the counterexample ---------------- *)

(* the first f _ _ is f a 1, whose X part has no g: the nested selector
   fails, the flattened one takes the second f *)
Goal forall (f : nat -> nat -> nat) (g : nat -> nat) (a b : nat), f a 1 + f b (g 2) = 0.
intros f g a b.
elpi sel_denote_expect "<f _ X | X> ; <g Y | Y>" "error".
elpi sel_denote_expect "<f _ (g Y) | Y>" "2.2.2.1".
elpi sel_normal_expect "<f _ X | X> ; <g Y | Y>" "<f _ X | X> ; <g Y | Y>".
elpi sel_to_ssr_expect "<f _ X | X> ; <g Y | Y>" "none".
elpi sel_to_ssr_expect "<f _ (g Y) | Y>" "[Y in f _ (g Y)]".
Abort.

(* GRAMMAR.md's side condition ("has an instance of C2 in its X part") is
   not enough: here the X part of the first f, h (g 1), has a g inside but
   is not one; nested and flattened differ (1 also occurs inside 2 = S 1,
   hence {1}) *)
Goal forall (f : nat -> nat -> nat) (g h : nat -> nat) (a b : nat),
  f a (h (g 1)) + f b (g 2) = 0.
intros f g h a b.
elpi sel_denote_expect "<f _ X | X> ; <g Y | Y>" "2.1.2.1.1".
elpi sel_denote_expect "<f _ (g Y) | Y>" "2.2.2.1".
elpi sel_normal_expect "<f _ X | X> ; <g Y | Y>" "<f _ X | X> ; <g Y | Y>".
elpi sel_to_ssr_expect "<f _ X | X> ; <g Y | Y>" "{1}[1]".
Abort.

(* the side condition holds: both agree, the normal form is flattened *)
Goal forall (f : nat -> nat -> nat) (g : nat -> nat) (a b : nat), f a (g 1) + f b (g 2) = 0.
intros f g a b.
elpi sel_denote_expect "<f _ X | X> ; <g Y | Y>" "2.1.2.1".
elpi sel_denote_expect "<f _ (g Y) | Y>" "2.1.2.1".
elpi sel_normal_expect "<f _ X | X> ; <g Y | Y>" "<f _ (g Y) | Y>".
elpi sel_to_ssr "<f _ X | X> ; <g Y | Y>".
elpi sel_robustness_expect "<f _ X | X> ; <g Y | Y>" "0 2.2".
Abort.

(* ---------------- In a hypothesis ---------------- *)

Goal forall (f : nat -> nat -> nat) (a c d : nat), c + d = f a (c + d) -> True.
intros f a c d H.
elpi sel_denote_expect "H" "<f a X | X>" "3.2".
elpi sel_to_ssr_expect "H" "<f a X | X>" "[X in f a X]".
elpi sel_to_ssr_expect "H" "3;2" "{2}[c + d]".
elpi sel_robustness_expect "H" "<_ + d>" "none".
Abort.
