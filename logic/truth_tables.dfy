include "propositional_logic.dfy"

module TruthTables {
	import opened PropositionalLogic

	const TruthTable_NOT :=
		map[
			false := true,
			true := false
		]

	const TruthTable_AND :=
		map[
			(false, false) := false, 
			(false, true ) := false, 
			(true , false) := false, 
			(true , true ) := true
		]

	const TruthTable_OR :=
		map[
			(false, false) := false, 
			(false, true ) := true, 
			(true , false) := true, 
			(true , true ) := true
		]

	const TruthTable_IMPLIES :=
		map[
			(false, false) := true, 
			(false, true ) := true, 
			(true , false) := false, 
			(true , true ) := true
		] // semantically: (p-->q) == ((not(p)\/q)

//	function Power(b: nat, n: nat): nat decreases n { if n == 0 then 1 else b*Power(b, n-1) }

	function AllRows(Vars: set<string>): set<map<string, bool>>
		requires Vars <= AllVariables
		decreases Vars
	{
		if Vars == {} then
			{map[]}
		else
			var x := FirstVariable(Vars);
			var other_rows := AllRows(Vars-{x});
			(set row: map<string, bool> | row in other_rows :: row[x := false]) +
			(set row: map<string, bool> | row in other_rows :: row[x := true])
	}

	function TruthTableColumn(f: PropositionalFormula, Vars: set<string>): map<map<string, bool>, bool>
		requires ValidFormula(f) && Variables(f) <= Vars <= AllVariables
		//ensures |TruthTableColumn(f, Vars).Keys| == Power(2, |Vars|)
		ensures forall m :: m in TruthTableColumn(f, Vars).Keys ==> m.Keys == Vars
		decreases f
	{
		map row: map<string, bool> | row.Keys == Vars && row in AllRows(Vars) ::
		match f
		case TRUE => true
		case FALSE => false
		case VAR(_) => assert f.name in Vars; row[f.name]
		case NOT(_) => TruthTable_NOT[TruthTableColumn(f.P, Vars)[row]]
		case AND(_, _) => TruthTable_AND[(TruthTableColumn(f.L, Vars)[row], TruthTableColumn(f.R, Vars)[row])]
		case OR(_, _) => TruthTable_OR[(TruthTableColumn(f.L, Vars)[row], TruthTableColumn(f.R, Vars)[row])]
		case IMPLIES(_, _) => TruthTable_IMPLIES[(TruthTableColumn(f.L, Vars)[row], TruthTableColumn(f.R, Vars)[row])]
	}

	predicate Value(f: PropositionalFormula, assignment: map<string, bool>)
		requires ValidFormula(f)
		requires Variables(f) <= assignment.Keys
		decreases f
	{
		match f
		case TRUE => true
		case FALSE => false
		case VAR(x) => assignment[x]
		case NOT(f1) => TruthTable_NOT[Value(f1, assignment)]
		case AND(f1, f2) => TruthTable_AND[(Value(f1, assignment), Value(f2, assignment))]
		case OR(f1, f2) => TruthTable_OR[(Value(f1, assignment), Value(f2, assignment))]
		case IMPLIES(f1, f2) => TruthTable_IMPLIES[(Value(f1, assignment), Value(f2, assignment))]
	}

	// satisfiable
	ghost predicate SAT(f: PropositionalFormula)
		requires ValidFormula(f)
	{
		exists assignment: map<string, bool> :: assignment.Keys == Variables(f) && Value(f, assignment) == true
	}

	// negation of disjunction is the conjunction of the negations
	lemma DeMorgan1(f1: PropositionalFormula, f2: PropositionalFormula, assignment: map<string, bool>)
		requires ValidFormula(f1) && Variables(f1) <= assignment.Keys
		requires ValidFormula(f2) && Variables(f2) <= assignment.Keys
		ensures Value(NOT(OR(f1, f2)), assignment) == Value(AND(NOT(f1), NOT(f2)), assignment)
	{
		var P1, P2 := Value(f1, assignment), Value(f2, assignment);
		calc {
			Value(NOT(OR(f1, f2)), assignment);
		==
			TruthTable_NOT[Value(OR(f1, f2), assignment)];
		==
			TruthTable_NOT[TruthTable_OR[(P1, P2)]];
		==
			TruthTable_AND[(TruthTable_NOT[P1], TruthTable_NOT[P2])];
		==
			TruthTable_AND[(Value(NOT(f1), assignment), Value(NOT(f2), assignment))];
		==
			Value(AND(NOT(f1), NOT(f2)), assignment);
		}
	}
}