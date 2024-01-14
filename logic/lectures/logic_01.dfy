/*

Logic and Set Theory - lecture 1

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Today:
∙ Introduction to Propositional logic
∙ Declarative sentences: atomic and compositional
	∙ Logical connectors: conjunction, disjunction, negation, implication
∙ Natural deduction: some proof rules


1.2 Natural deduction

[It is traditional in logic to use Greek letters. Lower-case letters are used to stand for formulas
and upper-case letters are used for sets of formulas. Here are some of the more commonly used
Greek letters, together with their pronunciation:

Lower-case: φ phi, ψ psi, χ chi, η eta, α alpha, β beta, γ gamma

Upper-case: Φ Phi, Ψ Psi, Γ Gamma, Δ Delta.]


A "sequent":

		φ₁, φ₂, ... , φₙ ⊦ ψ

Such a sequent is "valid" if a proof for it can be found.

The sequent for Examples 1.1 and 1.2 in the textbook:

		p ∧ ¬q ⟶ r, ¬r, p ⊦ q

1.2.1 Rules for natural deduction

∙ and-introduction

	 φ     ψ
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∧i
	  φ ∧ ψ

∙ and-elimination

	  φ ∧ ψ
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∧e₁
	    φ


	  φ ∧ ψ
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∧e₂
	    ψ


	1      p ∧ q        premise
	2      r            premise
	3      q            ∧e₂ 1
	4      q ∧ r        ∧i 3,2


	p ∧ q
	⎯⎯⎯⎯⎯ ∧e₂
	  q           r
	  ⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∧i
	       q ∧ r

The rules of double negation

∙ double-negation elimination

	 ¬¬φ
	⎯⎯⎯⎯⎯ ¬¬e
	  φ

∙ double-negation introduction

	  φ
	⎯⎯⎯⎯⎯ ¬¬i
	 ¬¬φ


Example 1.5: p, ¬¬(q ∧ r) ⊦ ¬¬p ∧ r

	1           p               premise
	2           ¬¬(q ∧ r)       premise
	3           ¬¬p             ¬¬i 1
	4           q ∧ r           ¬¬e 2
	5           r               ∧e₂ 4
	6           ¬¬p ∧ r         ∧i 3,5


Example 1.6: (p ∧ q) ∧ r, s ∧ t ⊦ q ∧ s

	1           (p ∧ q) ∧ r     premise
	2           s ∧ t           premise
	3           p ∧ q           ∧e₁ 1
	4           q               ∧e₂ 3
	5           s               ∧e₁ 2
	6           q ∧ s           ∧i 4,5

*/
module Logic_01 {
	method M1()
}