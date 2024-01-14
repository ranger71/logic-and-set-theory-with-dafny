include "../propositional_logic.dfy"

/*

Logic and Set Theory - lecture 4

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ Natural deduction: final proof rules

Today:
∙ Examples of provably equivalent formulas (page 29) + Example proof by case analysis: One of De Morgan's laws
∙ Propositional logic as a formal language
	∙ Well-formed formulas
	∙ Parse trees
	∙ Definitions in the verification-aware language Dafny (http://dafny.org/, https://github.com/dafny-lang/dafny/releases)


De Morgan's Laws:
∙ the negation of a conjunction is the disjunction of the negations
∙ the negation of a disjunction is the conjunction of the negations


1.3 Propositional logic as a formal language

Definition 1.27 The well-formed formulas of propositional logic are those
which we obtain by using the construction rules below, and only those,
finitely many times:

	atom: Every propositional atom p, q, r, ... and p1, p2, p3, ... is a well-formed 
	      formula.
	¬: If φ is a well-formed formula, then so is (¬φ).
	∧: If φ and ψ are well-formed formulas, then so is (φ ∧ ψ).
	∨: If φ and ψ are well-formed formulas, then so is (φ ∨ ψ).
	⟶: If φ and ψ are well-formed formulas, then so is (φ ⟶ ψ).

		φ ::= p | (¬φ) | (φ ∧ φ) | (φ ∨ φ) | (φ ⟶ φ)   // BNF for well-formed formulas in eq. (1.3) on page 33 

where p stands for any atomic proposition and each occurrence of φ to the
right of ::= stands for any already constructed formula.

		(((¬p) ∧ q) ⟶ (p ∧ (q ∨ (¬r))))   Is this a well-formed formula?

See Figure 1.3 (page 34): "A parse tree representing a well-formed formula."

The whole tree is a subtree of itself as well. So we can list all nine subformulas
of φ as
				p
				q
				r
				(¬p)
				((¬p) ∧ q)
				(¬r)
				(q ∨ (¬r))
				((p ∧ (q ∨ (¬r))))
				(((¬p) ∧ q) ⟶ (p ∧ (q ∨ (¬r)))).

*/
module Logic_04 {
	import opened PropositionalLogic

	method {:verify false} Main() {
		var f1 := IMPLIES(r, NOT(OR(p, q)));
		var str1 := FormulaToString(f1); // (r-->(¬(p\/q)))
		print str1, "\n";
		var f1' := FormulaFromString(str1);
		print FormulaToString(f1'), "\n";

		print FormulaToString(OR(NOT(C), AND(NOT(A), NOT(B)))), "\n";
		var str2 := "((¬C)\\/((¬A)/\\(¬B)))";
		var f2 := FormulaFromString(str2);
		var str2' := FormulaToString(f2);
		print str2', "\n";
		var f2' := FormulaFromString(str2');
		print FormulaToString(f2'), "\n";

		var f3 := IMPLIES(f1, f2);
		var str3 := FormulaToString(f3);
		print str3, "\n";
		var f3' := FormulaFromString(str3);
		print FormulaToString(f3'), "\n";

		print "The string ", str2, if WellFormedFormula(str2) then " is " else " is not ", "a well-formed formula.\n";
		print "The string ", str2 + ")", if WellFormedFormula(str2 + ")") then " is " else " is not ", "a well-formed formula.\n";
	}
}