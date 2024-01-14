module PropositionalLogic {

	const GlobalSymbolTable := ["p", "q", "r", "l", "s", "t", "A", "B", "C", "p1", "p2", "p3", "p4", "p5"]
	const AllVariables := set x | x in GlobalSymbolTable

	function IndexInGlobalSymbolTable(x: string): nat
		requires x in AllVariables
	{
		var i: nat :| i < |GlobalSymbolTable| && GlobalSymbolTable[i] == x;
		i
	}

	lemma GlobalSymbolTablePosition(x: string, i: nat)
		requires x in AllVariables && i == IndexInGlobalSymbolTable(x)
		ensures i < |GlobalSymbolTable| && GlobalSymbolTable[i] == x
	{}

	lemma ValidSymbolTable()
		ensures forall x | x in GlobalSymbolTable :: 
			IndexInGlobalSymbolTable(x) < |GlobalSymbolTable| && GlobalSymbolTable[IndexInGlobalSymbolTable(x)] == x
	{}

	datatype PropositionalFormula = TRUE | FALSE | VAR(name: string) |
		NOT(P: PropositionalFormula) | 
		AND(L: PropositionalFormula, R: PropositionalFormula) |
		OR(L: PropositionalFormula, R: PropositionalFormula) |
		IMPLIES(L: PropositionalFormula, R: PropositionalFormula)

	function Variables(f: PropositionalFormula): set<string>
		decreases f
	{
		match f
		case TRUE => {}
		case FALSE => {}
		case VAR(name) => {name}
		case NOT(f1) => Variables(f1) 
		case AND(f1, f2) => Variables(f1) + Variables(f2)
		case OR(f1, f2) => Variables(f1) + Variables(f2)
		case IMPLIES(f1, f2) => Variables(f1) + Variables(f2)
	}

	function FirstVariable(Vars: set<string>): string
		requires Vars <= AllVariables && |Vars| > 0
	{
		if GlobalSymbolTable[0] in Vars then GlobalSymbolTable[0]
		else if GlobalSymbolTable[1] in Vars then GlobalSymbolTable[1]
		else if GlobalSymbolTable[2] in Vars then GlobalSymbolTable[2]
		else if GlobalSymbolTable[3] in Vars then GlobalSymbolTable[3]
		else if GlobalSymbolTable[4] in Vars then GlobalSymbolTable[4]
		else if GlobalSymbolTable[5] in Vars then GlobalSymbolTable[5]
		else if GlobalSymbolTable[6] in Vars then GlobalSymbolTable[6]
		else if GlobalSymbolTable[7] in Vars then GlobalSymbolTable[7]
		else if GlobalSymbolTable[8] in Vars then GlobalSymbolTable[8]
		else if GlobalSymbolTable[9] in Vars then GlobalSymbolTable[9]
		else if GlobalSymbolTable[10] in Vars then GlobalSymbolTable[10]
		else if GlobalSymbolTable[11] in Vars then GlobalSymbolTable[11]
		else if GlobalSymbolTable[12] in Vars then GlobalSymbolTable[12]
		else assert Vars == {GlobalSymbolTable[13]}; GlobalSymbolTable[13]
	}

	predicate ValidVariableName(name: string) { name in AllVariables }

	predicate ValidFormula(f: PropositionalFormula) {
		Variables(f) <= AllVariables
	}

	function FormulaToString(f: PropositionalFormula): string
		requires ValidFormula(f)
		decreases f
	{
		match f
		case TRUE => "T"
		case FALSE => "F"
		case VAR(name) => name
		case NOT(f1) => "(¬" + FormulaToString(f1) + ")"
		case AND(f1, f2) => "(" + FormulaToString(f1) + "/\\" + FormulaToString(f2) + ")"
		case OR(f1, f2) => "(" + FormulaToString(f1) + "\\/" + FormulaToString(f2) + ")"
		case IMPLIES(f1, f2) => "(" + FormulaToString(f1) + "-->" + FormulaToString(f2) + ")"
	}

	predicate WellFormedAtomicFormula(str: string) {
		str == "T" || str == "F" || ValidVariableName(str)
	}

	predicate WellFormedNegation(str: string)
		decreases |str|, 1
	{
		|str| > 3 && str[0] == '(' && str[1] == '¬' && str[|str|-1] == ')' && WellFormedFormula(str[2..|str|-1])
	}

	// find the index of the binary connective ("/\", "\/" or "-->")
	// from index i, ignoring n closing parentheses first;
	// return the length of the string if no such closing parenthesis exists
	// or if too many closing parentheses precede it
	function BinaryConnectiveIndex(str: string, i: nat, n: nat): nat
		requires i <= |str|
		decreases |str|-i
	{
		if i == |str| then
			i
		else if n == 0 && str[i] == ')' then
			|str| // closing an un-opened parenthesis
		else if n == 0 && (str[i] == '/' || str[i] == '\\' || str[i] == '-') then
			i
		else if str[i] == ')' then
			BinaryConnectiveIndex(str, i+1, n-1)
		else if str[i] == '(' then
			BinaryConnectiveIndex(str, i+1, n+1)
		else
			BinaryConnectiveIndex(str, i+1, n)
	}

	predicate WellFormedBinaryConnective(str: string, connective: string)
		requires connective in {"/\\", "\\/", "-->"} // {'∧', '∨', '⟶'} 
		decreases |str|, 0
	{
		|str| >= 4 + |connective| && str[0] == '(' && str[|str|-1] == ')' &&
		var connective_index := BinaryConnectiveIndex(str, 1, 0);
		connective_index+|connective| < |str| &&
		str[connective_index..connective_index+|connective|] == connective &&
		WellFormedFormula(str[1..connective_index]) &&
		WellFormedFormula(str[connective_index+|connective|..|str|-1])
	}

	predicate WellFormedConjunction(str: string)
		decreases |str|, 1
	{
		WellFormedBinaryConnective(str, "/\\")
	}

	predicate WellFormedDisjunction(str: string)
		decreases |str|, 1
	{
		WellFormedBinaryConnective(str, "\\/")
	}

	predicate WellFormedImplication(str: string)
		decreases |str|, 1
	{
		WellFormedBinaryConnective(str, "-->")
	}

	predicate WellFormedFormula(str: string)
		decreases |str|, 2
	{
		WellFormedAtomicFormula(str) || WellFormedNegation(str) || WellFormedConjunction(str) ||
		WellFormedDisjunction(str) || WellFormedImplication(str)
	}

	// a simple parser, assuming full parentheses:
	function {:verify false} FormulaFromString(str: string): PropositionalFormula
		requires WellFormedFormula(str)
		decreases |str|
	{
		if WellFormedAtomicFormula(str) then
			if str == "T" then TRUE
			else if str == "F" then FALSE
			else assert ValidVariableName(str); VAR(str)
		else if WellFormedNegation(str) then
			NOT(FormulaFromString(str[2..|str|-1]))
		else if WellFormedConjunction(str) then 
			var connective_index := BinaryConnectiveIndex(str, 1, 0);
			AND(FormulaFromString(str[1..connective_index]), FormulaFromString(str[connective_index+2..|str|-1]))
		else if WellFormedDisjunction(str) then 
			var connective_index := BinaryConnectiveIndex(str, 1, 0);
			OR(FormulaFromString(str[1..connective_index]), FormulaFromString(str[connective_index+2..|str|-1]))
		else
			assert WellFormedImplication(str);
			var connective_index := BinaryConnectiveIndex(str, 1, 0);
			IMPLIES(FormulaFromString(str[1..connective_index]), FormulaFromString(str[connective_index+3..|str|-1]))
	}

	const p := VAR("p")
	const q := VAR("q")
	const r := VAR("r")
	const l := VAR("l")
	const s := VAR("s")
	const t := VAR("t")
	const A := VAR("A")
	const B := VAR("B")
	const C := VAR("C")
	const p1 := VAR("p1")
	const p2 := VAR("p2")
	const p3 := VAR("p3")
	const p4 := VAR("p4")
	const p5 := VAR("p5")
}