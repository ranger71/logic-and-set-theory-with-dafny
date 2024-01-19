/*

Logic and Set Theory - lecture 10

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ Proof theory of predicate logic: Natural deduction rules

Today:
∙ Quantifier equivalences
∙ Review the published solution to the set theory part of Assignment 1
  (relating the formal proofs with our rules of natural deduction)

Beyond today: Semantics of predicate logic
∙ Models, semantic entailment, soundness and completeness, semantics of equivalence, undecidability

Theorem 2.13 Let φ and ψ be formulas of predicate logic. Then we have
the following equivalences:

1. (a) ¬∀xφ ⊣⊢ ∃x¬φ
   (b) ¬∃xφ ⊣⊢ ∀x¬φ

2. Assuming that x is not free in ψ:

(Remember that ∀x φ ∧ ψ is implicitly bracketed as (∀x φ) ∧ ψ, 
by virtue of the binding priorities.)

   (a) ∀xφ ∧ ψ ⊣⊢ ∀x (φ ∧ ψ)
   (b) ∀xφ ∨ ψ ⊣⊢ ∀x (φ ∨ ψ)
   (c) ∃xφ ∧ ψ ⊣⊢ ∃x (φ ∧ ψ)
   (d) ∃xφ ∨ ψ ⊣⊢ ∃x (φ ∨ ψ)
   (e) ∀x (ψ ⟶ φ) ⊣⊢ ψ ⟶ ∀xφ
   (f) ∃x (φ ⟶ ψ) ⊣⊢ ∀xφ ⟶ ψ
   (g) ∀x (φ ⟶ ψ) ⊣⊢ ∃xφ ⟶ ψ
   (h) ∃x (ψ ⟶ φ) ⊣⊢ ψ ⟶ ∃xφ

3. (a) ∀xφ ∧ ∀xψ ⊣⊢ ∀x (φ ∧ ψ)
   (b) ∃xφ ∨ ∃xψ ⊣⊢ ∃x (φ ∨ ψ)

4. (a) ∀x ∀y φ ⊣⊢ ∀y ∀xφ
   (b) ∃x ∃y φ ⊣⊢ ∃y ∃xφ

Let's prove 1(a): ¬∀xφ ⊣⊢ ∃x¬φ in two parts: first "¬∀xφ ⊢ ∃x¬φ" and then "∃x¬φ ⊢ ¬∀xφ"

¬∀xφ ⊢ ∃x¬φ

		       1       ¬∀xφ             premise
		┌────────────────────────────────────────────────────────────┐
		│      2       ¬∃x¬φ            assumption
		│┌──────────────────────────────────────────────────────────┐
		││     3   x0
		││┌────────────────────────────────────────────────────────┐
		│││    4       ¬φ[x0/x]         assumption
		│││    5       ∃x¬φ             ∃x i 4 [with φ (of the rule) being ¬φ]
		│││    6       ⊥                ¬e 5,2
		││└────────────────────────────────────────────────────────┘
		││     7       φ[x0/x]          PBC 4-6
		│└──────────────────────────────────────────────────────────┘
		│      8       ∀xφ              ∀x i 3-7
		│      9       ⊥                ¬e 8,1
		└────────────────────────────────────────────────────────────┘
		       10      ∃x¬φ             PBC 2-9

∃x¬φ ⊢ ¬∀xφ

		       1       ∃x¬φ             premise
		┌────────────────────────────────────────────────────────────┐
		│      2       ∀xφ              assumption
		│┌──────────────────────────────────────────────────────────┐
		││     3   x0
		││     4       ¬φ[x0/x]         assumption
		││     5       φ[x0/x]          ∀x e 2
		││     6       ⊥                ¬e 5,4
		│└──────────────────────────────────────────────────────────┘
		│      7       ⊥                ∃x e 1,3-6
		└────────────────────────────────────────────────────────────┘
		       8       ¬∀xφ             ¬i 2-7
*/
module Logic_10 { method M10() {} }