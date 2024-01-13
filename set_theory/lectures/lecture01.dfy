/*

Logic and Set Theory - lecture 1

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hourse: Wednesdays 18-20

Today: introduction to logic:
- syntax and semantics
- propositions: atomic and composite
- truth tables
- logical connectors/operators: conjunction, disjunction, negation, implication (later in the semester), equivalence

Language: Dafny
Recommended Environment: Visual Studio Code (VS Code)

Q26:

B said that A said that A is a Knave

due to P below, B must be lying

if (C is a knight) {
	C is a knight
	C said that B is a knave
	B must be a knave
	A said that A is a Knight
}
else {
	C is Knave
	B is knight
	A said he was a knave
	which contradicts P below!!!
}
C must be a knight, B must be a knave!!!

if (A is Knave) {
	A would answer that he is a knight
}
else {
	A is a knight
	A would answer that he is a knight
}
P: So anyway A would anser he was a knight!!!

 Naively, we could have examined all cases:

S is the set of all Knights
if S == {A,B,C} NO
else if S == {A,B} NO 
else if S == {B,C} NO
else if S == {A,C} good 
else if S == {} NO 
else if S == {A} NO 
else if S == {B} NO 
else if S == {C} good

Q28

A makes the following statement: "At least one of us is a knave"
(in other words: A is knave || B is knave)

If A is knave, we know that !(A is knave || B is knave)
And according to the De Morgan (1) law (see below), this is logically equivalent to:
!(A is knave) && !(B is knave) which is in turn equivalent to:
A is knight && B is knight
so we reached a contraditiction (with the assumption that A was knave);

conclusion: the only possible option is that A is knight.
Since A said that at least one of them is knave, the only possible option is that
B is knave.

Answer: A is knight and B is knave

We needed help, since there's negation of a composite proposition!

The truth table of negation:

 P    !P
 F    T
 T    F

The truth table of conjunction (AND, &&):

 P  Q  (P && Q)
 F  F  F
 F  T  F
 T  F  F
 T  T  T

The truth table of disjunction (OR, ||):

 P  Q  (P || Q)
 F  F  F
 F  T  T
 T  F  T
 T  T  T (the so-called inclusive or, in contrast to exclusive-or)

What is the truth table of the proposition !(P || Q)

 P  Q  (P || Q)  !(P || Q)
 F  F  F         T
 F  T  T         F
 T  F  T         F
 T  T  T         F

De Morgan 1: negation of disjunction is the conjunction of the negations

!(P || Q) == !P && !Q

We need to check that the 4th column is equal to the 7th column:

 P  Q  (P || Q)  !(P || Q)   !P     !Q    (!P && !Q)
 F  F  F         T           T      T     T   
 F  T  T         F           T      F     F
 T  F  T         F           F      T     F
 T  T  T         F           F      F     F

Q29

A says "Either I am a knave or B is a knight."

P: A is knave
Q: B is knight

A says: P || Q

If A is a knight, B must be a knight too; why?

If A is knave, P is true, we have !(P || Q)
By De Morgan (1), this is:
!P && !Q
P and !P is a contradiction

P is false, A is a knight;
and Q? must be true! 

So we have !P and Q:
A is not a knave (it is a knight) and
B is a knight too.
*/

module Lecture01 {
//int x = 3*(y / 4) + (z*3);
// bool b1 = (b2 || (x > 5) && y < 6);
// bool b3 = (b2 || (x > 5) && y < 6);
	const GlobalSymbolTable: map<nat, string> := map[0 := "A", 1 := "B", 2 := "C", 3 := "P", 4 := "Q", 5 := "R"]

	datatype PropositionalFormula = TRUE | FALSE | VAR(id: nat) |
		NOT(P: PropositionalFormula) | 
		AND(L: PropositionalFormula, R: PropositionalFormula) |
		OR(L: PropositionalFormula, R: PropositionalFormula) |
		IMPLIES(L: PropositionalFormula, R: PropositionalFormula) |
		FOLLOWS_FROM(L: PropositionalFormula, R: PropositionalFormula) |
		EQUIVALENT(L: PropositionalFormula, R: PropositionalFormula)

	function Identifiers(f: PropositionalFormula): set<nat>
		decreases f
	{
		match f
		case TRUE => {}
		case FALSE => {}
		case VAR(id) => {id}
		case NOT(f1) => Identifiers(f1) 
		case AND(f1, f2) => Identifiers(f1) + Identifiers(f2)
		case OR(f1, f2) => Identifiers(f1) + Identifiers(f2)
		case IMPLIES(f1, f2) => Identifiers(f1) + Identifiers(f2)
		case FOLLOWS_FROM(f1, f2) => Identifiers(f1) + Identifiers(f2)
		case EQUIVALENT(f1, f2) => Identifiers(f1) + Identifiers(f2)
	}

	function Variables(f: PropositionalFormula): set<string>
		requires Identifiers(f) <= GlobalSymbolTable.Keys
	{
		set id | id in Identifiers(f) :: GlobalSymbolTable[id]
	}

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
		]

	const TruthTable_FOLLOWS_FROM :=
		map[
			(false, false) := true, 
			(false, true ) := false, 
			(true , false) := true, 
			(true , true ) := true
		]

	const TruthTable_EQUIVALENT :=
		map[
			(false, false) := true, 
			(false, true ) := false, 
			(true , false) := false, 
			(true , true ) := true
		]

/*
example:
f = OR(AND(Var("bool1"), Var("bool2")), NOT(Var("bool1")) // ("bool1" && "bool2") || !"bool1"
f1 = AND(Var("bool1"), Var("bool2")), f2 = NOT(Var("bool1")
A: "bool1"
B: "bool2"
[(false, false) := TruthTable_OR[(TruthTableColumn_4Rows(AND(Var("bool1"), Var("bool2")), A, B)[(false, false)],
                                  TruthTableColumn_4Rows(NOT(Var("bool1"), A, B)[(false, false)])]
 (false, true)  := TruthTable_OR[(TruthTableColumn_4Rows(AND(Var("bool1"), Var("bool2")), A, B)[(false, true)],
                                  TruthTableColumn_4Rows(NOT(Var("bool1"), A, B)[(false, true)])]
 (true,  false) := TruthTable_OR[(TruthTableColumn_4Rows(AND(Var("bool1"), Var("bool2")), A, B)[(true, false)],
                                  TruthTableColumn_4Rows(NOT(Var("bool1"), A, B)[(true, false)])]
 (true,  true)  := TruthTable_OR[(TruthTableColumn_4Rows(AND(Var("bool1"), Var("bool2")), A, B)[(true, true)],
                                  TruthTableColumn_4Rows(NOT(Var("bool1"), A, B)[(true, true)])]
 ]
== // continue with the recursive calls (evaluating each Var case, showing here the result of the result of the if ... then .. else)
[(false, false) := TruthTable_OR[(TruthTable_AND[((map P, Q :: (P, Q) := P)[(false, false)], (map P, Q :: (P, Q) := Q)[(false, false)])],
                                  TruthTable_NOT[(map P, Q :: (P, Q) := P)[(false, false)])],
 (false, true)  := TruthTable_OR[(TruthTable_AND[((map P, Q :: (P, Q) := P)[(false, true)], (map P, Q :: (P, Q) := Q)[(false, true)])],
                                  TruthTable_NOT[(map P, Q :: (P, Q) := P)[(false, true)])],
 (true,  false) := TruthTable_OR[(TruthTable_AND[((map P, Q :: (P, Q) := P)[(true, false)], (map P, Q :: (P, Q) := Q)[(true, false)])],
                                  TruthTable_NOT[(map P, Q :: (P, Q) := P)[(true, false)])],
 (true,  true)  := TruthTable_OR[(TruthTable_AND[((map P, Q :: (P, Q) := P)[(true, true)], (map P, Q :: (P, Q) := Q)[(true, true)])],
                                  TruthTable_NOT[(map P, Q :: (P, Q) := P)[(true, true)])]
 ]
== // evaluating each (map P, Q :: ...)
[(false, false) := TruthTable_OR[(TruthTable_AND[(false, false)],
                                  TruthTable_NOT[false])],
 (false, true)  := TruthTable_OR[(TruthTable_AND[(false, true)],
                                  TruthTable_NOT[false])],
 (true,  false) := TruthTable_OR[(TruthTable_AND[(true, false)],
                                  TruthTable_NOT[true])],
 (true,  true)  := TruthTable_OR[(TruthTable_AND[(true, true)],
                                  TruthTable_NOT[true])]
 ]
== // evaluating the inner truth table references (the AND and the NOT)
[(false, false) := TruthTable_OR[(false,
                                  true)],
 (false, true)  := TruthTable_OR[(false,
                                  true)],
 (true,  false) := TruthTable_OR[(false,
                                  false)],
 (true,  true)  := TruthTable_OR[(true,
                                  false)]
 ]
== // one last evaluation step
[(false, false) := true,
 (false, true)  := true,
 (true,  false) := false,
 (true,  true)  := true
 ]

Does this result make sense? Is this the expected column in the truth table of f("bool1", "bool2")?
Recalling "f" this is ("bool1" && "bool2") || !"bool1", YES, the answer is as expected. Cool!

The next challenge is to generalize this to a table of any formula, not just with 2 variables.

*/
	// TODO: prove
/*
	ghost function {:verify false} TruthTableColumn_4Rows(f: PropositionalFormula, VarIds: set<nat>): map<map<nat, bool>, bool>
		requires ValidFormula(f) && Identifiers(f) <= VarIds && |VarIds| == 2
		decreases f
	{
		map row: map<nat, bool> | row.Keys == VarIds && row in AllRows(VarIds) ::
		match f
		case TRUE => true
		case FALSE => false
		case VAR(id) => row[id]
		case NOT(f1) => TruthTable_NOT[TruthTableColumn_4Rows(f1, VarIds)[row]]
		case AND(f2, f3) => TruthTable_AND[(TruthTableColumn_4Rows(f2, VarIds)[row], TruthTableColumn_4Rows(f3, VarIds)[row])]
		case OR(f4, f5) => TruthTable_OR[(TruthTableColumn_4Rows(f4, VarIds)[row], TruthTableColumn_4Rows(f5, VarIds)[row])]
		case IMPLIES(f6, f7) => TruthTable_IMPLIES[(TruthTableColumn_4Rows(f6, VarIds)[row], TruthTableColumn_4Rows(f7, VarIds)[row])]
		case FOLLOWS_FROM(f8, f9) => TruthTable_FOLLOWS_FROM[(TruthTableColumn_4Rows(f8, VarIds)[row], TruthTableColumn_4Rows(f9, VarIds)[row])]
		case EQUIVALENT(f10, f11) => TruthTable_AND[(TruthTableColumn_4Rows(f10, VarIds)[row], TruthTableColumn_4Rows(f11, VarIds)[row])]
	}
*/
	function Power(b: nat, n: nat): nat decreases n { if n == 0 then 1 else b*Power(b, n-1) }

/* TODO: remove? (not needed anymore, right?)

	predicate IsSmallerString(str1: string, str2: string) {
		if str2 == "" then false
		else if str1 == "" then true else
		assert |str1| > 0 && |str2| > 0;
		var c1, c2 := str1[0] as int, str2[0] as int;
		if c1 < c2 then true else
		if c1 > c2 then false else
		IsSmallerString(str1[1..], str2[1..])
	}
*/

function SmallestIdentifier(VarIds: set<nat>, i: nat, j: int): nat
		requires i in VarIds && j < i
		requires VarIds <= GlobalSymbolTable.Keys
		decreases j
	{
		if j < 0 then i else var k := if j in VarIds then j else i;
		SmallestIdentifier(VarIds, k, j-1)
/*
		var i :| i in VarIds;
		if |VarIds| == 1 then
			i
		else
			var j := SmallestIdentifier(set x | x in VarIds && x != i);
			if i < j then i else j
*/
	}

	function AllRows(VarIds: set<nat>): set<map<nat, bool>>
		requires VarIds <= GlobalSymbolTable.Keys
	{
		if VarIds == {} then
			{map[]}
		else
			//var x: string :| x in V && forall y :: y in V-{x} ==> x ;
			var i :| i in VarIds;
			var x := SmallestIdentifier(VarIds, i, i-1); //forall y :: y in VarIds-{x} ==> y < x;
			var other_rows := AllRows(VarIds-{x});
			(set row: map<nat, bool> | row in other_rows :: row[x := false]) +
			(set row: map<nat, bool> | row in other_rows :: row[x := true])
	}

	// TODO: prove
	function {:verify false} TruthTableColumn(f: PropositionalFormula, VarIds: set<nat>): map<map<nat, bool>, bool>
		requires ValidFormula(f) && Identifiers(f) <= VarIds
		ensures |TruthTableColumn(f, VarIds).Keys| == Power(2, |VarIds|)
		ensures forall m :: m in TruthTableColumn(f, VarIds).Keys ==> m.Keys == VarIds
		decreases f
	{
		map row: map<nat, bool> | row.Keys == VarIds && row in AllRows(VarIds) :: //if f.VAR? then row[f.id] else if f.AND? then 
		//TruthTable_AND[(TruthTableColumn(f.L, VarIds)[row], TruthTableColumn(f.R, VarIds)[row])] else false
		match f
		case TRUE => true
		case FALSE => false
		case VAR(_) => assert f.id in VarIds; row[f.id]
		case NOT(_) => TruthTable_NOT[TruthTableColumn(f.P, VarIds)[row]]
		case AND(_, _) => TruthTable_AND[(TruthTableColumn(f.L, VarIds)[row], TruthTableColumn(f.R, VarIds)[row])]
		case OR(_, _) => TruthTable_OR[(TruthTableColumn(f.L, VarIds)[row], TruthTableColumn(f.R, VarIds)[row])]
		case IMPLIES(_, _) => TruthTable_IMPLIES[(TruthTableColumn(f.L, VarIds)[row], TruthTableColumn(f.R, VarIds)[row])]
		case FOLLOWS_FROM(_, _) => TruthTable_FOLLOWS_FROM[(TruthTableColumn(f.L, VarIds)[row], TruthTableColumn(f.R, VarIds)[row])]
		case EQUIVALENT(_, _) => TruthTable_EQUIVALENT[(TruthTableColumn(f.L, VarIds)[row], TruthTableColumn(f.R, VarIds)[row])]
	}

	// TODO: consider removing this
	ghost function SetToSeq(s: set): seq
		decreases s
	{
		if |s| == 0 then [] else var e :| e in s; [e] + SetToSeq(s-{e})
	}
/*
	ghost predicate Value'(f: PropositionalFormula, assignment: map<string, bool>)
		requires Variables(f) <= assignment.Keys
		decreases f
	{
		var V := SetToSeq(Variables(f));
		if |V| == 2
		then
			var A, B := V[0], V[1];
			assume Variables(f) == {A, B} && A in assignment.Keys && B in assignment.Keys;
			TruthTableColumn_4Rows(f, A, B)[(assignment[A], assignment[B])]
		else Value(f, assignment)
	}*/

	predicate Value(f: PropositionalFormula, assignment: map<nat, bool>)
		requires ValidFormula(f)
		requires Identifiers(f) <= assignment.Keys
		decreases f
	{
		match f
		case TRUE => true
		case FALSE => false
		case VAR(id) => assignment[id]
		case NOT(f1) => TruthTable_NOT[Value(f1, assignment)]
		case AND(f1, f2) => TruthTable_AND[(Value(f1, assignment), Value(f2, assignment))]
		case OR(f1, f2) => TruthTable_OR[(Value(f1, assignment), Value(f2, assignment))]
		case IMPLIES(f1, f2) => TruthTable_IMPLIES[(Value(f1, assignment), Value(f2, assignment))]
		case FOLLOWS_FROM(f1, f2) => TruthTable_FOLLOWS_FROM[(Value(f1, assignment), Value(f2, assignment))]
		case EQUIVALENT(f1, f2) => TruthTable_EQUIVALENT[(Value(f1, assignment), Value(f2, assignment))]
	}

	predicate IsAlphanumeric(c: char) {
		'0' <= c <= '9' || 'a' <= c <= 'z' || 'A' <= c <= 'Z' // TODO: make sure this indeed amounts to being alphanumeric (in Dafny)
	}

	predicate ValidVariableName(name: string) {
		name != "T" && name != "F" && name != "NOT" && // generalize by defining a global set of keywords
		forall i :: 0 <= i < |name| ==> var c := name[i]; IsAlphanumeric(c) || c == '_'
	}

	predicate ValidSymbolTable() {
		|GlobalSymbolTable.Keys| == |GlobalSymbolTable.Values| && // no duplicates
		forall x :: x in GlobalSymbolTable.Values ==> ValidVariableName(x)
	}

	predicate ValidFormula(f: PropositionalFormula) {
		ValidSymbolTable() && Identifiers(f) <= GlobalSymbolTable.Keys
	}

	function FormulaToString(f: PropositionalFormula): string
		requires ValidFormula(f)
		decreases f
	{
		match f
		case TRUE => "T"
		case FALSE => "F"
		case VAR(id) => GlobalSymbolTable[id]
		case NOT(f1) => "NOT(" + FormulaToString(f1) + ")" 
		case AND(f1, f2) => "(" + FormulaToString(f1) + "/\\" + FormulaToString(f2) + ")"
		case OR(f1, f2) => "(" + FormulaToString(f1) + "\\/" + FormulaToString(f2) + ")"
		case IMPLIES(f1, f2) => "(" + FormulaToString(f1) + "==>" + FormulaToString(f2) + ")"
		case FOLLOWS_FROM(f1, f2) => "(" + FormulaToString(f1) + "<==" + FormulaToString(f2) + ")"
		case EQUIVALENT(f1, f2) => "(" + FormulaToString(f1) + "<==>" + FormulaToString(f2) + ")"
	}

/*	function FormulaFromString(str: string): PropositionalFormula
	{
		// TODO: parse the string into a formula in case it indeed well-formed (in some syntax we'll have to define);
		// and then we may want to prove a lemma that for any f, FormulaFromString(StringFromFormula(f) == f
	}*/

	ghost predicate SAT(f: PropositionalFormula)
		requires ValidFormula(f)
	{
		exists assignment: map<nat, bool> :: assignment.Keys == Identifiers(f) && Value(f, assignment) == true
	}

	// TODO: remove this?
	function Identifier(name: string): nat
		requires name in GlobalSymbolTable.Values
	{
		var id :| id in GlobalSymbolTable.Keys && GlobalSymbolTable[id] == name;
		id
	}

	const A := assert GlobalSymbolTable[0] == "A"; VAR(0) //VAR(id("A"))
	const B := assert GlobalSymbolTable[1] == "B"; VAR(1) //VAR(id("B"))
	const C := assert GlobalSymbolTable[2] == "C"; VAR(2) //VAR(id("C"))
	const P := assert GlobalSymbolTable[3] == "P"; VAR(3) //VAR(id("P"))
	const Q := assert GlobalSymbolTable[4] == "Q"; VAR(4) //VAR(id("Q"))
	const R := assert GlobalSymbolTable[5] == "R"; VAR(5) //VAR(id("R"))
	
	// TODO: prove
	lemma {:verify false} LemmaGlobalVariables()
		ensures GlobalSymbolTable.Keys == {A.id, B.id, C.id, P.id, Q.id, R.id}
	{}

	// TODO: prove
	lemma {:verify false} LemmaValidSymbolTable()
		ensures ValidSymbolTable()
	{}

/*
	method FirstFormula() {
		var f1: PropositionalFormula := AND(P, Q); // P && Q
		var a1 := map[P.id := true, Q.id := false];
		assert ValidFormula(f1) by {
			//assert ValidSymbolTable();
			//assert Identifiers(f1) == {P.id, Q.id} <= GlobalSymbolTable.Keys;
			// TODO: prove...
			LemmaGlobalVariables();
			LemmaValidSymbolTable();
		}
		print "The value of the formula ", FormulaToString(f1), " with the assignment [\"P\" == true, \"Q\" == false] is ",
			Value(f1, a1);
		var VarIds := Identifiers(f1);
		assert ValidFormula(f1);
		assert VarIds == {P.id, Q.id};
		assert |VarIds| == 2 by { assert P.id != Q.id; }
		print "The ultimate column in the truth table of the formula ", FormulaToString(f1), " is ",
			TruthTableColumn_4Rows(f1, VarIds);
		var a2 := map[P.id := true, Q.id := true];
		print "\nThe value of the formula ", FormulaToString(f1), " with the assignment [\"P\" == true, \"Q\" == true] is ",
			Value(f1, a2);
		print "\n";

		assert SAT(f1) by {
			assert ValidFormula(f1);
			assert a2.Keys == Identifiers(f1) && Value(f1, a2) == true;
		}
	}
*/
	// negation of disjunction is the conjunction of the negations
	lemma DeMorgan1(f1: PropositionalFormula, f2: PropositionalFormula, assignment: map<nat, bool>)
		requires ValidFormula(f1) && Identifiers(f1) <= assignment.Keys
		requires ValidFormula(f2) && Identifiers(f2) <= assignment.Keys
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
/*
f1: A && B
f2: T

A=T, B=F

f1: T && F = F
f2: T

!(T || F)
F
=?
F
(T && F)
(!F && F)
(!(T && F) && F)
(!(T && F) && F)[A := T, B := F]
(!(A && B) && F)[A := T, B := F]
(!(A && B) && !T)[A := T, B := F]
(!f1 && !f2)[A := T, B := F]

The column of:
AND(NOT(f1), NOT(f2)
in its truth table has the same boolean values in each row as the column of:
NOT(OR(f1, f2))
in its truth table.

 f1 | f2 | NOT(f1) | NOT(f2) | AND(NOT(f1), NOT(f2)) | OR(f1, f2) | NOT(OR(f1, f2)) | AND(NOT(f1), NOT(f2)) <==> NOT(OR(f1, f2))
 F  | F  | T       | T       | T                     | F          | T               | T
 F  | T  | T       | F       | F                     | T          | F               | T
 T  | F  | F       | T       | F                     | T          | F               | T
 T  | T  | F       | F       | F                     | T          | F               | T
*/
/*	lemma DeMorgan2(f1: PropositionalFormula, f2: PropositionalFormula)
		requires |Variables(f1) + Variables(f2)| <= 2
		ensures TruthTableColumn_4Rows(NOT(OR(f1, f2)), assignment) == Value(AND(NOT(f1), NOT(f2)), assignment)
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
	}*/

	method Main() {
		//FirstFormula();
		var VarIds := {0, 1, 2};
		var i: int :| i in VarIds;
		print SmallestIdentifier(VarIds, i, i-1), "\n";
		//var other_rows := AllRows(VarIds-{i});
		//print other_rows, "\n";
		//print AllRows(VarIds-{i}), "\n";//AllRows({0, 1});
		//print (set row: map<nat, bool> | row in other_rows :: row[i := false]) +
		//	(set row: map<nat, bool> | row in other_rows :: row[i := true]);
		//var m: map<nat, bool> := map[];
		//print {m[1:=false]}+{m[1:=true]}, "\n";
		print GlobalSymbolTable, "\n";
		var f1 := IMPLIES(VAR(2), NOT(OR(VAR(0), VAR(1))));//AND(P, Q); // P && Q
		assert ValidFormula(f1) by { LemmaGlobalVariables(); LemmaValidSymbolTable(); }
		print FormulaToString(f1), "\n";
		assert Identifiers(f1) <= VarIds;
		print TruthTableColumn(f1, VarIds), "\n";
		var f2 := OR(NOT(VAR(2)), AND(NOT(VAR(0)), NOT(VAR(1))));
		assert ValidFormula(f2) by { LemmaGlobalVariables(); LemmaValidSymbolTable(); }
		assert Identifiers(f2) <= VarIds;
		print FormulaToString(f2), "\n";
		print TruthTableColumn(f2, VarIds), "\n";
		var f3 := EQUIVALENT(f1, f2);
		assert ValidFormula(f3) by { LemmaGlobalVariables(); LemmaValidSymbolTable(); }
		assert Identifiers(f3) <= VarIds;
		print FormulaToString(f3), "\n";
		print TruthTableColumn(f3, VarIds), "\n";
	}
}