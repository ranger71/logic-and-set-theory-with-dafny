include "../propositional_logic.dfy"
include "../truth_tables.dfy"

/*

Logic and Set Theory - lecture 5

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ De Morgan's laws + Propositional logic as a formal language (Well-formed formulas + Parse trees)

Today:
∙ The semantics of a propositional formula by Truth Tables

semantically (p-->q) is equivalent to (not(p)\/q)

let's prove this claim with truth tables:

	p        q      (p-->q)      (¬p)            ((¬p)\/q)
	========================================================
	F        F      T            T               T
	F        T      T            T               T
	T        F      F            F               F
	T        T      T            F               T

*/
module Logic_05_G2 {
	import opened PropositionalLogic
	import opened TruthTables

	method FirstFormula() {
		var f1: PropositionalFormula := AND(p, q); // (p/\q)
		var a1 := map[p.name := true, q.name := false];
		assert ValidFormula(f1);
		print "The value of the formula ", FormulaToString(f1), " with the assignment [\"p\" == true, \"q\" == false] is ",
			Value(f1, a1), "\n";
		// The value of the formula (p/\q) with the assignment ["p" == true, "q" == false] is false

		var Vars := Variables(f1);
		assert ValidFormula(f1);
		assert Vars == {p.name, q.name};
		assert |Vars| == 2 by { assert p.name != q.name; }
		print "The ultimate column in the truth table of the formula ", FormulaToString(f1), " is ",
			TruthTableColumn(f1, Vars), "\n";

		/* The ultimate column in the truth table of the formula (p/\q) is
		
		map[
			map[p := false, q := false] := false, 
			map[p := false, q := true] := false, 
			map[p := true, q := false] := false, 
			map[p := true, q := true] := true]
	
		*/
	}

	method Main() {
		FirstFormula();

		// let's try to prove one of the De Morgan laws with truth tables:
		var f1, f2 := NOT(OR(p, q)), AND(NOT(p), NOT(q));
/*
		                      (p\/q)          (¬(p\/q))            (¬p)           (¬q)          ((¬p)/\(¬q))
		p          q          OR(p, q)        NOT(OR(p, q))        NOT(p)         NOT(q)        AND(NOT(p), NOT(q))
		===========================================================================================================
		F          F          F               T                    T              T             T
		F          T          T               F                    T              F             F
		T          F          T               F                    F              T             F
		T          T          T               F                    F              F             F
*/
		var Vars1 := Variables(f1);
		var Vars2 := Variables(f2);
		print "The ultimate column in the truth table of the formula ", FormulaToString(f1), " is ",
			TruthTableColumn(f1, Vars1), "\n";
		/*

		The ultimate column in the truth table of the formula (¬(p\/q)) is 

		map[
			map[p := false, q := false] := true, 
			map[p := false, q := true] := false, 
			map[p := true, q := false] := false, 
			map[p := true, q := true] := false]
		*/

		print "The ultimate column in the truth table of the formula ", FormulaToString(f2), " is ",
			TruthTableColumn(f2, Vars2), "\n";

		/*

		The ultimate column in the truth table of the formula ((¬p)/\(¬q)) is 

		map[
			map[p := false, q := false] := true, 
			map[p := false, q := true] := false, 
			map[p := true, q := false] := false, 
			map[p := true, q := true] := false]
*/
		var VarNames := {"p", "q", "r"};
		var Vars := {p, q, r};
		print FirstVariable(VarNames), "\n"; // p
		f1 := IMPLIES(r, NOT(OR(p, q)));
		assert ValidFormula(f1);
		print FormulaToString(f1), "\n";
		assert Variables(f1) <= VarNames;

		/*

		p     q     r       (p\/q)       (¬(p\/q))       (r-->(¬(p\/q)))
		================================================================
		F     F     F       F            T               T
		F     F     T       F            T               T
		F     T     F       T            F               T
		F     T     T       T            F               F
		T     F     F       T            F               T
		T     F     T       T            F               F
		T     T     F       T            F               T
		T     T     T       T            F               F

		*/

		print TruthTableColumn(f1, VarNames), "\n";

		/*

		map[
			map[p := false, q := false, r := false] := true, 
			map[p := false, q := false, r := true] := true, 
			map[p := false, q := true, r := false] := true, 
			map[p := false, q := true, r := true] := false, 
			map[p := true, q := false, r := false] := true,
			map[p := true, q := false, r := true] := false, 
			map[p := true, q := true, r := false] := true, 
			map[p := true, q := true, r := true] := false]
		*/

		f2 := OR(NOT(r), AND(NOT(p), NOT(q)));
		assert ValidFormula(f2);
		assert Variables(f2) <= VarNames;
		print FormulaToString(f2), "\n"; // ((¬r)\/((¬p)/\(¬q)))

		print TruthTableColumn(f2, VarNames), "\n";
		/*
		map[
			map[p := false, q := false, r := false] := true, 
			map[p := false, q := false, r := true] := true, 
			map[p := false, q := true, r := false] := true, 
			map[p := true, q := false, r := false] := true, 
			map[p := false, q := true, r := true] := false, 
			map[p := true, q := false, r := true] := false, 
			map[p := true, q := true, r := false] := true, 
			map[p := true, q := true, r := true] := false]
		*/
	}
}
