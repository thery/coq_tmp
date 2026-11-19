// Mock-up: the five examples in the free syntax (examples/*.free.md).
// typst compile --input brackets=on|off: with or without the margin bars
#import "lib.typ": *
#show: proof-text.with(lang: "en", numbers: false)
#set page(foreground: bracket-layer)

#std.text(size: 0.85em, fill: luma(90))[Mock-up of the *free* syntax: proof nodes are spans inside the paragraphs#";" the marks `[...]{.p}` never show. #if structure-mode == "on" [Each subproof has a thin bar in the left margin, one bar per depth.] else if structure-mode == "corners" [Each subproof is between two small grey corners.] else [No mark of the structure in the PDF: only the colours.] Hand-written Typst, not produced by a reader.]

#example("praeclarum", "(UITP 2006)")
#prose[Let #var($x, y, z, t : "Prop"$). If #hyp($x → z$) and #hyp($y → t$) then #claim($(x ∧ y) → (z ∧ t)$).]
#prose[#ps("p1", 0)[Suppose #hyp($x ∧ y$). #ps("p1.1", 1)[#ps("p1.1.1", 2)[We have #claim($x$)], so by #fact($x → z$) we get #claim($z$).] #ps("p1.2", 1)[#ps("p1.2.1", 2)[We have #claim($y$)], so by #fact($y → t$) we get #claim($t$).] Altogether we have #claim($z ∧ t$).]]

#example("square_pos", "(UITP 2006)")
#prose[Let #var($a, b ∈ ℤ$). If #hyp($0 < a < b$) then #claim($a a < b b$).]
#prose[#ps("s1", 0)[It is equivalent to prove #claim($0 < b b - a a$). #ps("s1.1", 1)[That can also be written as #claim($0 < (b + a)(b - a)$). #ps("s1.1.1", 2)[From #fact($0 < a < b$) we have #claim($0 < b + a ∧ 0 < b - a$).]]]]

#example("exp_pos", "(UITP 2006)")
#prose[Let #var($x ∈ ℝ$) and #var($y ∈ ℤ$). If #hyp($0 < x$), to prove #claim($0 < x^y$), we have three cases: #ps("e1", 0)[if #hyp($0 < y$) then #claim($x^1 ≤ x^y$)]#";" #ps("e2", 0)[if #hyp($0 = y$) then #claim($x^y = 1$)]#";" #ps("e3", 0)[if #hyp($y < 0$) then #claim($x^y = 1 / x^(-y)$)].]

#example("praeclarum", "(xtext)")
#prose[Let #var($x, y, z, t : "Prop"$). Assume #hyp($(x → z) ∧ (y → t)$) #name("h1") and #hyp($x ∧ y$) #name("h2"). We prove #claim($z ∧ t$).]
#prose[#ps("x1", 0)[Going back to the definition of and (#jb("and_ind")) in #jb("h1"), we prove #claim($z ∧ t$): #ps("x1.1", 1)[assume #hyp($x → z$) #name("i") and #hyp($y → t$) #name("j")#";" going back to the definition of and (#jb("and_ind")) in #jb("h2"), we prove #claim($z ∧ t$): #ps("x1.1.1", 2)[assume #hyp($x$) #name("k") and #hyp($y$) #name("l")#";" #ps("x1.1.1.1", 3)[applying #jb("i") to #jb("k"), we have #claim($z$)]#";" #ps("x1.1.1.2", 3)[applying #jb("j") to #jb("l"), we have #claim($t$)]#";" so by definition of and (#jb("conj")), we have #claim($z ∧ t$).]]]]

#example("Trans_Inv", "(xtext)")
#prose[Let #var($E : "Set"$). Let #var($R : "Rel" E$). Assume #hyp($"Trans" E R$) #name("h"). We prove #claim($"Trans" E ("Inv" E R)$).]
#prose[#ps("t1", 0)[Let us choose arbitrarily #var($x, y, z ∈ E$)#";" assume #hyp($"Inv" E R x y$) #name("h1") and #hyp($"Inv" E R y z$) #name("h2"). #ps("t1.1", 1)[By #jb("h") we have $"Trans" E R$, that is #claim($∀ x_0 y_0 z_0 ∈ E, R x_0 y_0 → R y_0 z_0 → R x_0 z_0$).] #ps("t1.2", 1)[By #jb("h2") we have $"Inv" E R y z$, that is #claim($R z y$).] #ps("t1.3", 1)[By #jb("h1") we have $"Inv" E R x y$, that is #claim($R y x$).] By application, we have $R z x$, that is #claim($"Inv" E R x z$).] #ps("t2", 0)[We have proved #claim($∀ x_0 y_0 z_0 ∈ E, "Inv" E R x_0 y_0 → "Inv" E R y_0 z_0 → "Inv" E R x_0 z_0$)], that is $"Trans" E ("Inv" E R)$.]

#legend5
