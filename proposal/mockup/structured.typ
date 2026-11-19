// Mock-up: the five examples in the structured syntax (examples/*.structured.md)
#import "lib.typ": *
#show: proof-text.with(lang: "en", numbers: false)

#std.text(size: 0.85em, fill: luma(90))[Mock-up of the *structured* syntax: one list item per proof node, sub-items are its subproofs, a closing paragraph after the sub-items is the node's conclusion line. Hand-written Typst, not produced by a reader.]

#example("praeclarum", "(UITP 2006)")
#statement[Let #var($x, y, z, t : "Prop"$). If #hyp($x → z$) and #hyp($y → t$) then #claim($(x ∧ y) → (z ∧ t)$).]
#item(0)[Suppose #hyp($x ∧ y$).]
#item(1)[We get #claim($z$) by #fact($x → z$), since]
#item(2)[we have #claim($x$).]
#item(1)[We get #claim($t$) by #fact($y → t$), since]
#item(2)[we have #claim($y$).]
#closing(0)[Altogether we have #claim($z ∧ t$).]

#example("square_pos", "(UITP 2006)")
#statement[Let #var($a, b ∈ ℤ$). If #hyp($0 < a < b$) then #claim($a a < b b$).]
#item(0)[It is equivalent to prove #claim($0 < b b - a a$).]
#item(1)[That can also be written as #claim($0 < (b + a)(b - a)$).]
#item(2)[From #fact($0 < a < b$) we have #claim($0 < b + a ∧ 0 < b - a$).]

#example("exp_pos", "(UITP 2006)")
#statement[Let #var($x ∈ ℝ$) and #var($y ∈ ℤ$). If #hyp($0 < x$), to prove #claim($0 < x^y$), we have three cases:]
#item(0)[If #hyp($0 < y$) then #claim($x^1 ≤ x^y$).]
#item(0)[If #hyp($0 = y$) then #claim($x^y = 1$).]
#item(0)[If #hyp($y < 0$) then #claim($x^y = 1 / x^(-y)$).]

#example("praeclarum", "(xtext)")
#statement[Let #var($x, y, z, t : "Prop"$). Assume #hyp($(x → z) ∧ (y → t)$) #name("h1") and #hyp($x ∧ y$) #name("h2"). We prove #claim($z ∧ t$).]
#item(0)[Going back to the definition of and (#jb("and_ind")) in #jb("h1"), we prove #claim($z ∧ t$):]
#item(1)[Assume #hyp($x → z$) #name("i") and #hyp($y → t$) #name("j"). Going back to the definition of and (#jb("and_ind")) in #jb("h2"), we prove #claim($z ∧ t$):]
#item(2)[Assume #hyp($x$) #name("k") and #hyp($y$) #name("l").]
#item(3)[Applying #jb("i") to #jb("k"), we have #claim($z$).]
#item(3)[Applying #jb("j") to #jb("l"), we have #claim($t$).]
#closing(2)[So by definition of and (#jb("conj")), we have #claim($z ∧ t$).]

#example("Trans_Inv", "(xtext)")
#statement[Let #var($E : "Set"$). Let #var($R : "Rel" E$). Assume #hyp($"Trans" E R$) #name("h"). We prove #claim($"Trans" E ("Inv" E R)$).]
#item(0)[Let us choose arbitrarily #var($x, y, z ∈ E$)#";" assume #hyp($"Inv" E R x y$) #name("h1") and #hyp($"Inv" E R y z$) #name("h2").]
#item(1)[By #jb("h") we have $"Trans" E R$, that is #claim($∀ x_0 y_0 z_0 ∈ E, R x_0 y_0 → R y_0 z_0 → R x_0 z_0$).]
#item(1)[By #jb("h2") we have $"Inv" E R y z$, that is #claim($R z y$).]
#item(1)[By #jb("h1") we have $"Inv" E R x y$, that is #claim($R y x$).]
#closing(0)[By application, we have $R z x$, that is #claim($"Inv" E R x z$).]
#item(0)[We have proved #claim($∀ x_0 y_0 z_0 ∈ E, "Inv" E R x_0 y_0 → "Inv" E R y_0 z_0 → "Inv" E R x_0 z_0$), that is $"Trans" E ("Inv" E R)$.]

#legend5
