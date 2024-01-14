# logic-and-set-theory-with-dafny

Material for a logic and set theory course written in the verification-aware programming language Dafny

## Dafny 2024 @ POPL talk on the LST course (London, 14 January 2024):

"Teaching Logic and Set Theory with Dafny" by Ran Ettinger and Hezi Daniel, Israel Academic College in Ramat Gan

A second-year course on Logic and Set Theory to computer science students:

1) Dafny as a proof assistant: set theory
2) Dafny as a (verification-aware) programming language: propositional logic
3) Dafny as a teaching assistant!
	- providing instant feedback for students
	- help in the grading process
		- see 31 vs 14-step proof story below

## Sources and Inspiration

- Set Theory: An “Introduction to Set Theory and Logic” course by Prof. Uri Abraham at Ben-Gurion University

- Logic: “Logic in Computer Science: Modelling and Reasoning about Systems” by Huth and Ryan

- For both: “Dafny Power User: Different Styles of Proofs” by K. Rustan M. Leino

## Selected Proofs (from past and present course assignment exercises)

- Five set-theory-related examples: Dafny as a proof assistant
- Four propositional-logic-related examples: Dafny as a (verification-aware) programming language

## Set-theory-related examples: Dafny as a proof assistant

- distributivity of set union over intersection
- set difference is NOT associative
- domain and range of the inverse (binary) relation
- bijective functions / cardinal equivalence
- equivalence relations

## Propositional-logic-related examples: Dafny as a (verification-aware) programming language

- three natural deduction sequent validity proofs
- one truth table example

## Future directions

- More automation for predicate logic
- More automation in grading (Is it actually desirable?)
- Comparison with logic courses based on other proof assistants (such as Lean and Coq)
