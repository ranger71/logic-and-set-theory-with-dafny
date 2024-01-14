/*

Logic and Set Theory - lecture 2

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ Introduction to Propositional logic
∙ Declarative sentences: atomic and compositional
	∙ Logical connectors: conjunction, disjunction, negation, implication
∙ Natural deduction: some proof rules

Today:
∙ Natural deduction: some more proof rules
	∙ Logical implication: elimination and introduction rules (with "boxes" of inference)
	∙ The rules for disjunction (logical "or")

The rule for eliminating implication (modus ponens)

∙ implies-elimination

	φ     φ ⟶ ψ
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ⟶e
	   ψ

¬p ∧ q, ¬p ∧ q ⟶ r ∨ ¬p ⊦ r ∨ ¬p

	1     ¬p ∧ q               premise
	2     ¬p ∧ q ⟶ r ∨ ¬p     premise
	3     r ∨ ¬p               ⟶e 1,2

∙ modus tollens

	 φ ⟶ ψ     ¬ψ
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  MT
	      ¬φ


p ⟶ (q ⟶ r), p, ¬r ⊢ ¬q

	1     p ⟶ (q ⟶ r)       premise
	2     p                   premise
	3     ¬r                  premise
	4     q ⟶ r              ⟶e 2,1
	5     ¬q                  MT 4,3


p ⟶ q, ¬q ⊢ ¬p

p ⟶ q ⊢ ¬q ⟶ ¬p


∙ implies introduction

	┌───┐
	│ φ │  
	│   │
	│ ∙ │
	│ ∙ │
	│ ∙ │
	│   │ 
	│ ψ │
	└───┘
	⎯⎯⎯⎯⎯⎯⎯  ⟶i
	φ ⟶ ψ
	

Example 1.9: ¬q ⟶ ¬p ⊢ p ⟶ ¬¬q

	1      ¬q ⟶ ¬p        premise
	     ┌────────────────────────────┐
	2    │ p               assumption │
	3    │ ¬¬p             ¬¬i 2      │
	4    │ ¬¬q             MT 1,3     │
	     └────────────────────────────┘
	5      p ⟶ ¬¬q        ⟶i 2-4


∙ disjunction introduction (logical "or" introduction)

	   φ
	⎯⎯⎯⎯⎯⎯⎯⎯  ∨i₁
	 φ ∨ ψ


	   ψ
	⎯⎯⎯⎯⎯⎯⎯⎯  ∨i₂
	 φ ∨ ψ


∙ disjunction elimination ("or" elimination)

	        ┌───┐   ┌───┐
	        │ φ │   │ ψ │
	        │   │   │   │
	        │ ∙ │   │ ∙ │
	        │ ∙ │   │ ∙ │
	        │ ∙ │   │ ∙ │
	        │   │   │   │
	        │ χ │   │ χ │
	φ ∨ ψ   └───┘   └───┘	 
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∨e
	        χ            


p ∨ q ⊢ q ∨ p


	1      p ∨ q             premise
	     ┌────────────────────────────┐
	2    │ p               assumption │
	3    │ q ∨ p           ∨i₂ 2      │
	     └────────────────────────────┘
	     ┌────────────────────────────┐
	4    │ q               assumption │
	5    │ q ∨ p           ∨i₁ 4      │
	     └────────────────────────────┘
	6      q ∨ p             ∨e 1,2-3,4-5   



Example 1.16: q ⟶ r ⊢ p ∨ q ⟶ p ∨ r

	1      q ⟶ r          premise
	     ┌──────────────────────────────┐
	2    │ p ∨ q           assumption   │
	     │┌────────────────────────────┐│
	3    ││ p               assumption ││
	4    ││ p ∨ r           ∨i₁ 3      ││
	     │└────────────────────────────┘│
	     │┌────────────────────────────┐│
	5    ││ q               assumption ││
	6    ││ r               ⟶e 5,1    ││
	7    ││ p ∨ r           ∨i₁ 3      ││
	     │└────────────────────────────┘│
	8    │ p ∨ r           ∨e 2,3-4,5-7 │
	     └──────────────────────────────┘
	9      p ∨ q ⟶ p ∨ r        ⟶i 2-8

*/
module Logic_02 {
	method M1()
}