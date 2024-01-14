/*

Logic and Set Theory - lecture 3

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19 (בתיאום מראש, במייל)

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ Natural deduction: some more proof rules
	∙ Logical implication: elimination and introduction rules (with "boxes" of inference)
	∙ The rules for disjunction (logical "or")

Today:
∙ Natural deduction: final proof rules
	∙ Some extras following last week: theorems (Definition 1.10 + Remark 1.12),
	                                   proof structure (Fig. 1.1), 
	                                   logical equivalence ("⊣⊢" Examples 1.13 and 1.14),
	                                   the copy rule (Example 1.18) and self implication
	∙ Contradiction
	∙ Single negation introduction and elimination
	∙ Derived rules: PBC, Excluded Middle

Definition 1.10	Logical formulas φ with valid sequent ⊢ φ are theorems.

Example 1.11	Here is an example of a theorem whose proof utilises most
of the rules introduced so far:

	     ┌──────────────────────────────────────────────────────┐
	1    │    q ⟶ r                               assumption
	     │┌────────────────────────────────────────────────────┐
	2    ││   ¬q ⟶ ¬p                             assumption
	     ││┌──────────────────────────────────────────────────┐
	3    │││  p                                    assumption
	4    │││  ¬¬p                                  ¬¬i 3
	5    │││  ¬¬q                                  MT 2,4
	6    │││  q                                    ¬¬e 5
	7    │││  r                                    ⟶e 1,6
	     ││└──────────────────────────────────────────────────┘
	8    ││   p ⟶ r                               ⟶i 3−7
	     │└────────────────────────────────────────────────────┘
	9    │    (¬q ⟶ ¬p) ⟶ (p ⟶ r)              ⟶i 2−8
	     └──────────────────────────────────────────────────────┘
	10    (q ⟶ r) ⟶ ((¬q ⟶ ¬p) ⟶ (p ⟶ r))    ⟶i 1−9



                                     ⟶
                                  ╱      ╲
                                 ╱        ╲
                                ╱          ╲
                               ╱╲           ╲
                              ╱  ╲           ╲
                             ╱    ╲           ╲
                            ╱      ╲           ╲
                           ╱ q ⟶ r ╲           ⟶
                           ──────────        ╱      ╲
                                            ╱        ╲
                                           ╱          ╲
                                          ╱╲           ╲
                                         ╱  ╲           ╲
                                        ╱    ╲           ╲
                                       ╱      ╲           ╲
                                      ╱¬q ⟶ ¬p╲          ⟶
                                      ──────────        ╱      ╲
                                                       ╱        ╲
                                                      ╱          ╲
                                                     ╱╲           ╲
                                                    ╱  ╲           ╲
                                                   ╱    ╲           ╲
                                                  ╱      ╲           ╲
                                                 ╱    p   ╲           r
                                                 ──────────


Figure 1.1. Part of the structure of the formula (q ⟶ r) ⟶ ((¬q ⟶ ¬p) ⟶ (p ⟶ r))
to show how it determines the proof structure.


The sequent ⊢ (q ⟶ r) ⟶ ((¬q ⟶ ¬p) ⟶ (p ⟶ r)) is valid,
showing that (q ⟶ r) ⟶ ((¬q ⟶ ¬p) ⟶ (p ⟶ r)) is another theorem.

Remark 1.12 We may transform any proof of φ₁, φ₂, . . . , φₙ ⊢ ψ
in such a way into a proof of the theorem ⊢ φ₁ ⟶ (φ₂ ⟶ (φ3 ⟶ (···⟶(φₙ ⟶ ψ) ... )))
by ‘augmenting’ the previous proof with n lines of the rule ⟶i applied to
φₙ, φₙ₋₁,. . . , φ₁ in that order.


Logical equivalence.

Example 1.13: p ∧ q ⟶ r ⊢ p ⟶ (q ⟶ r):

	1        p ∧ q ⟶ r                           premise
	     ┌────────────────────────────────────────────────────┐
	2    │   p                                    assumption
	     │┌──────────────────────────────────────────────────┐
	3    ││  q                                    assumption
	4    ││  p ∧ q                                ∧i 2,3
	5    ││  r                                    ⟶e 1, 4
	     │└──────────────────────────────────────────────────┘
	6    │   q ⟶ r                               ⟶i 3−5
	     └────────────────────────────────────────────────────┘
	7       p ⟶ (q ⟶ r)                         ⟶i 2−6


Example 1.14: the ‘converse’ of the sequent above is valid, too:

	1      p ⟶ (q ⟶ r)  premise
	     ┌────────────────────────────┐
	2    │ p ∧ q           assumption
	3    │ q               ∧e₁ 2
	4    │ r               ∧e₂ 2
	5    │ q ⟶ r          ⟶e 1,3
	6    │ r               ⟶e 5,4
	     └────────────────────────────┘
	7      p ∧ q ⟶ r      ⟶i 2−6


	p ∧ q ⟶ r ⊣⊢ p ⟶ (q ⟶ r)

The copy rule.

⊢ p ⟶ (q ⟶ p)

	     ┌──────────────────────────────┐
	1    │  p               assumption
	     │┌────────────────────────────┐
	2    ││ q               assumption
	3    ││ p               copy 1
	     │└────────────────────────────┘
	4    │  q ⟶ p          ⟶i 2−3
	     └──────────────────────────────┘
	5       p ⟶ (q ⟶ p)   ⟶i 1−4



	1      p               premise

p ⊢ p

	     ┌────────────────────────────┐
	1    │ p               assumption │
	     └────────────────────────────┘
	2      p ⟶ p          ⟶i 1−1

⊢ p ⟶ p

Another option:

	     ┌────────────────────────────┐
	1    │ p               assumption │
	2    │ p               copy 1     │
	     └────────────────────────────┘
	3      p ⟶ p          ⟶i 1−2


The rules for negation.

Definition 1.19  Contradictions are expressions of the form "φ ∧ ¬φ" or
"¬φ ∧ φ", where φ is any formula.

We denote a contradiction with the symbol "⊥" (pronounced "bottom").

Examples of such contradictions:

	∙ r ∧ ¬r
	∙ (p ⟶ q) ∧ ¬(p ⟶ q)
	∙ ¬(r ∨ s ⟶ q) ∧ (r ∨ s ⟶ q)
	
	¬(r ∨ s ⟶ q) ∧ (r ∨ s ⟶ q) ⊣⊢ (p ⟶ q) ∧ ¬(p ⟶ q)

	p ∧ ¬p ⊢ q
	
∙ bottom-elimination

	 ⊥
	⎯⎯⎯⎯  ⊥e
	 φ

∙ not-elimination

	 φ     ¬φ
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ¬e
	    ⊥


Example 1.20: ¬p ∨ q ⊢ p ⟶ q

	1       ¬p ∨ q          premise
	     ┌───────────────────────────────┐
	2    │  p               assumption
	     │┌─────────────────────────────┐
	3    ││ ¬p              assumption
	4    ││ ⊥               ¬e 2,3
	5    ││ q               ⊥e 4
	     │└─────────────────────────────┘
	     │┌─────────────────────────────┐
	6    ││ q               assumption
	7    ││ q               copy 6
	     │└─────────────────────────────┘
	8    │  q               ∨e 1,3-5,6-7
	     └───────────────────────────────┘
	9       p ⟶ q          ⟶i 2−8

∙ not-introduction

	┌───┐
	│ φ │  
	│   │
	│ ∙ │
	│ ∙ │
	│ ∙ │
	│   │ 
	│ ⊥ │
	└───┘
	⎯⎯⎯⎯⎯⎯  ¬i
	 ¬φ


Example 1.21: p ⟶ q, p⟶ ¬q ⊢ ¬p

	   1    p ⟶ q           premise
	   2    p ⟶ ¬q          premise
	┌───────────────────────────────────┐
	│  3    p                assumption 
	│  4    q                ⟶e 3,1
	│  5    ¬q               ⟶e 3,2
	│  6    ⊥                ¬e 4,5
	└───────────────────────────────────┘
	   7    ¬p               ¬i 3−6


p ⟶ ¬p ⊢ ¬p

	   1    p ⟶ ¬p          premise
	┌───────────────────────────────────┐
	│  2    p                assumption 
	│  3    ¬p               ⟶e 2,1
	│  4    ⊥                ¬e 2,3
	└───────────────────────────────────┘
	   5    ¬p               ¬i 2−4


Example 1.22  p ⟶ (q ⟶ r), p, ¬r ⊢ ¬q  (without using MT)

	   1    p ⟶ (q ⟶ r)    premise
	   2    p                premise
	   3    ¬r               premise
	┌───────────────────────────────────┐
	│  4    q                assumption 
	│  5    q ⟶ r           ⟶e 1, 2
	│  6    r                ⟶e 4,5
	│  7    ⊥                ¬e 6,3
	└───────────────────────────────────┘
	   8    ¬q            ¬i 4−7


Example 1.23 (= Examples 1.1 and 1.2 from the first lecture): p ∧¬q ⟶ r, ¬r, p |− q

	   1    p ∧ ¬q ⟶ r    premise
	   2    ¬r             premise
	   3    p              premise
	┌────────────────────────────────┐
	│  4    ¬q             assumption 
	│  5    p ∧ ¬q         ∧i 3,4
	│  6    r              ⟶e 5,1
	│  7    ⊥              ¬e 6,2
	└────────────────────────────────┘
	   8    ¬¬q            ¬i 4−7
	   9    q              ¬¬e 8


1.2.2 Derived rules

∙ modus tollens

	 φ ⟶ ψ     ¬ψ
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  MT
	      ¬φ


	   1    φ ⟶ ψ     premise
	   2    ¬ψ         premise
	┌─────────────────────────────┐
	│  3    φ          assumption 
	│  4    ψ          ⟶e 3,1
	│  5    ⊥          ¬e 4,2
	└─────────────────────────────┘
	   6    ¬φ             ¬i 3−5


∙ double-negation introduction

	  φ
	⎯⎯⎯⎯⎯ ¬¬i
	 ¬¬φ


	   1    φ          premise
	┌─────────────────────────────┐
	│  2    ¬φ         assumption 
	│  3    ⊥          ¬e 1,2
	└─────────────────────────────┘
	   4    ¬¬φ        ¬i 2−3


∙ proof by contradiction (PBC)

	┌─────┐
	│ ¬φ  │  
	│     │
	│  ∙  │
	│  ∙  │
	│  ∙  │
	│     │ 
	│  ⊥  │
	└─────┘
	⎯⎯⎯⎯⎯⎯⎯⎯  PBC
	   φ


Suppose we have a proof of ⊥ from ¬φ. By ⟶i, we can transform this into
a proof of ¬φ ⟶ ⊥ and proceed as follows:

	   1    ¬φ ⟶ ⊥    given
	┌─────────────────────────────┐
	│  2    ¬φ         assumption 
	│  3    ⊥          ⟶e 2,1
	└─────────────────────────────┘
	   4    ¬¬φ        ¬i 2−3
	   5    φ          ¬¬e 4


∙ law of the excluded middle (LEM)

	 
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  LEM
	   φ ∨ ¬φ


	     ┌───────────────────────────────┐
	1    │  ¬(φ ∨ ¬φ)       assumption
	     │┌─────────────────────────────┐
	2    ││ φ               assumption
	3    ││ φ ∨ ¬φ          ∨i₁ 2
	4    ││ ⊥               ¬e 3,1
	     │└─────────────────────────────┘
	5    │  ¬φ              ¬e 2-4
	6    │  φ ∨ ¬φ          ∨i₂ 5
	7    │  ⊥               ¬e 6,1
	     └───────────────────────────────┘
	8    │  ¬¬(φ ∨ ¬φ)      ¬i 1-7
	9    │  φ ∨ ¬φ          ¬¬e 8


Example 1.24 [Not shown in class] p ⟶ q ⊢ ¬p ∨ q

	   1    p ⟶ q     premise
	   2    ¬p ∨ p     LEM
	┌─────────────────────────────┐
	│  3    ¬p         assumption 
	│  4    ¬p ∨ q     ∨i₁ 3
	└─────────────────────────────┘
	┌─────────────────────────────┐
	│  5    p          assumption 
	│  6    q          ⟶e 5,1
	│  7    ¬p ∨ q     ∨i₂ 6
	└─────────────────────────────┘
	   8    ¬p ∨ q     ∨e 2,3−4,5−7

*/
module Logic_03 {
	method M1()
}