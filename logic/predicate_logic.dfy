module PredicateLogic {

	const TempVariableNames := ["x'"]
	const GlobalSymbolTable := ["p", "q", "r", "s", "t", "A", "B", "C", "p1", "p2", "p3", "p4", "p5", "x", "y", "z"] + TempVariableNames
	const AllVariables := set x | x in GlobalSymbolTable

	const FunctionNames := ["c", "c1", "c2", "c3", "t1", "t2", "0", "1", "+", "f", "f1", "f2", "f3", "g", "g1", "g2", "g3", "h", "h1", "h2", "h3"]

	const PredicateNames := ["=", ">", "P", "Q", "R", "S", "P1", "P2", "P3"]

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

	datatype Term = VAR(name: string) | F(name: string, terms: seq<Term>)

	datatype Formula = TRUE | FALSE |
		P(name: string, terms: seq<Term>) |
		NOT(phi: Formula) | 
		AND(L: Formula, R: Formula) |
		OR(L: Formula, R: Formula) |
		IMPLIES(L: Formula, R: Formula) |
		EXISTS(x: string, phi: Formula) |
		FORALL(x: string, phi: Formula)

	function FunctionsInTerm(term: Term): set<string> {
		match term
		case VAR(_) => {}
		case F(name, terms) => {name} + FunctionsInTerms(terms)
	}

	function VariablesInTerm(term: Term): set<string> {
		match term
		case VAR(name) => {name}
		case F(_, terms) => VariablesInTerms(terms)
	}

	function FunctionsInTerms(terms: seq<Term>): set<string> {
		if |terms| == 0 then {} else FunctionsInTerm(terms[0]) + FunctionsInTerms(terms[1..])
	}

	function VariablesInTerms(terms: seq<Term>): set<string> {
		if |terms| == 0 then {} else VariablesInTerm(terms[0]) + VariablesInTerms(terms[1..])
	}

	function FreeAndBoundVariables(f: Formula): set<string>
		decreases f
	{
		match f
		case TRUE => {}
		case FALSE => {}
		case P(name, terms) => VariablesInTerms(terms)
		case NOT(f1) => FreeAndBoundVariables(f1) 
		case AND(f1, f2) => FreeAndBoundVariables(f1) + FreeAndBoundVariables(f2)
		case OR(f1, f2) => FreeAndBoundVariables(f1) + FreeAndBoundVariables(f2)
		case IMPLIES(f1, f2) => FreeAndBoundVariables(f1) + FreeAndBoundVariables(f2)
		case EXISTS(_, f1) => FreeAndBoundVariables(f1)
		case FORALL(_, f1) => FreeAndBoundVariables(f1)
	}

	// names of all predicates occurring in the formula
	function PredicatesInFormula(f: Formula): set<string>
		decreases f
	{
		match f
		case TRUE => {}
		case FALSE => {}
		case P(name, terms) => {name}
		case NOT(f1) => PredicatesInFormula(f1) 
		case AND(f1, f2) => PredicatesInFormula(f1) + PredicatesInFormula(f2)
		case OR(f1, f2) => PredicatesInFormula(f1) + PredicatesInFormula(f2)
		case IMPLIES(f1, f2) => PredicatesInFormula(f1) + PredicatesInFormula(f2)
		case EXISTS(x1, f1) => PredicatesInFormula(f1)
		case FORALL(x1, f1) => PredicatesInFormula(f1)
	}

	// names of all functions occurring in the formula
	function FunctionsInFormula(f: Formula): set<string>
		decreases f
	{
		match f
		case TRUE => {}
		case FALSE => {}
		case P(name, terms) => FunctionsInTerms(terms)
		case NOT(f1) => FunctionsInFormula(f1) 
		case AND(f1, f2) => FunctionsInFormula(f1) + FunctionsInFormula(f2)
		case OR(f1, f2) => FunctionsInFormula(f1) + FunctionsInFormula(f2)
		case IMPLIES(f1, f2) => FunctionsInFormula(f1) + FunctionsInFormula(f2)
		case EXISTS(x1, f1) => FunctionsInFormula(f1)
		case FORALL(x1, f1) => FunctionsInFormula(f1)
	}

	// names of all free variables occurring in the formula
	function Variables(f: Formula): set<string>
		decreases f
	{
		match f
		case TRUE => {}
		case FALSE => {}
		case P(name, terms) => VariablesInTerms(terms)
		case NOT(f1) => Variables(f1) 
		case AND(f1, f2) => Variables(f1) + Variables(f2)
		case OR(f1, f2) => Variables(f1) + Variables(f2)
		case IMPLIES(f1, f2) => Variables(f1) + Variables(f2)
		case EXISTS(x1, f1) => Variables(f1) - {x1}
		case FORALL(x1, f1) => Variables(f1) - {x1}
	}

	predicate ValidVariableName(name: string) { name in AllVariables && name !in TempVariableNames }

	predicate ValidVariableName'(name: string) { name in AllVariables }

	predicate ValidFunctionName(name: string) { name in FunctionNames }

	predicate ValidPredicateName(name: string) { name in PredicateNames }

	predicate ValidFormula(f: Formula)
		decreases f
	{
		(forall vname <- FreeAndBoundVariables(f) :: ValidVariableName(vname)) &&
		(forall fname <- FunctionsInFormula(f) :: ValidFunctionName(fname)) &&
		(forall pname <- PredicatesInFormula(f) :: ValidPredicateName(pname))
	}

	predicate ValidFormula'(f: Formula)
		decreases f
	{
		ValidFormula(f) ||
		(forall vname <- FreeAndBoundVariables(f) :: ValidVariableName'(vname))
	}

	predicate ValidTerm(t: Term)
		decreases t
	{
		(forall vname <- VariablesInTerm(t) :: ValidVariableName(vname)) &&
		(forall fname <- FunctionsInTerm(t) :: ValidFunctionName(fname))
		// match t
		// case VAR(name) => ValidVariableName(name)
		// case F(name, terms) => ValidFunctionName(name) && ValidTerms(terms)
	}

	predicate ValidTerms(terms: seq<Term>) {
		forall t <- terms :: ValidTerm(t)
	}

	predicate FreeForSub(t: Term, f: Formula, x: string)
		requires ValidTerm(t)
		requires ValidFormula'(f)
	{
		true // TODO: define
	}

	function SubstituteInTerm(t_old: Term, x: string, t_new: Term): Term {
		match t_old
		case VAR(name) => if name == x then t_new else t_old // the actual (conditional) substitution
		case F(name, terms) => F(name, SubstituteInTerms(terms, x, t_new))
	}

	// should be trivially true; still, TODO: prove
	lemma {:verify false} SubInTermId(t_old: Term, x: string)
		requires ValidTerm(t_old) || (VariablesInTerm(t_old) <= AllVariables) // TODO: second disjunct needed?
		requires x !in VariablesInTerm(t_old)
		ensures forall t_new | ValidTerm(t_new) :: SubstituteInTerm(t_old, x, t_new) == t_old
	{}

	function SubstituteInTerms(terms: seq<Term>, x: string, t: Term): seq<Term>
	{
		if |terms| == 0 then [] else [SubstituteInTerm(terms[0], x, t)] + SubstituteInTerms(terms[1..], x, t)
	}

/*
	// should be trivially true; still, TODO: prove
	lemma {:verify false} SubInTermsId(terms: seq<Term>, x: string)
		requires forall t <- terms :: ValidTerm'(t)
		requires x !in VariablesInTerms(terms)
		ensures forall t <- terms, t_new | ValidTerm'(t_new) :: ValidTerm'(t) && SubstituteInTerms(terms, x, t) == terms
	{}
*/

	// TODO: verify (trivial, right?)
	lemma {:verify false} ValidSubformula(f: Formula)
		requires ValidFormula'(f)
		ensures forall f1 | f1 < f :: ValidFormula'(f1)
	{}

	function Substitute(f: Formula, x: string, t: Term): Formula
		requires ValidFormula'(f)
		requires x in TempVariableNames
		requires ValidTerm(t)
		requires FreeForSub(t, f, x)
		decreases f
	{
		match f
		case TRUE => TRUE
		case FALSE => FALSE
		case P(name, terms) => P(name, SubstituteInTerms(terms, x, t))
		case NOT(f1) => NOT(Substitute(f1, x, t))
		case AND(f1, f2) => AND(Substitute(f1, x, t), Substitute(f2, x, t))
		case OR(f1, f2) => OR(Substitute(f1, x, t), Substitute(f2, x, t))
		case IMPLIES(f1, f2) => IMPLIES(Substitute(f1, x, t), Substitute(f2, x, t))
		case EXISTS(x1, f1) => ValidSubformula(f); if x1 == x then f else EXISTS(x1, Substitute(f1, x, t))
		case FORALL(x1, f1) => ValidSubformula(f); if x1 == x then f else FORALL(x1, Substitute(f1, x, t))
	}

	// should be trivially true; still, TODO: prove
	lemma {:verify false} SubId(f: Formula, x: string)
		requires ValidFormula(f)
		requires x !in Variables(f)
		ensures forall t | ValidTerm(t) :: Substitute(f, x, t) == f
	{}

	// TODO: re-verify (following the change in definition of ValidFormula'?)
	function {:verify false} TermToString(term: Term): string
		requires ValidTerm(term)
	{
		match term
		case VAR(name) =>
			name
		case F(name, terms) =>
			if |terms| == 0 then
				name
			else 
				name + "(" +  TermsToString(terms) + ")"
	}

	function TermsToString(terms: seq<Term>): string
		requires ValidTerms(terms)
	{
		if |terms| == 0 then
			""
		else if |terms| == 1 then
			TermToString(terms[0])
		else
			TermToString(terms[0]) + "," + TermsToString(terms[1..])
	}

	// TODO: re-verify (following the change in definition of ValidFormula)
	function {:verify false} FormulaToString(f: Formula): string
		requires ValidFormula(f)
		decreases f
	{
		match f
		case TRUE => "T"
		case FALSE => "F"
		case P(name, terms) => name + "(" + TermsToString(terms) + ")"
		case NOT(f1) => "(¬" + FormulaToString(f1) + ")"
		case AND(f1, f2) => "(" + FormulaToString(f1) + "/\\" + FormulaToString(f2) + ")"
		case OR(f1, f2) => "(" + FormulaToString(f1) + "\\/" + FormulaToString(f2) + ")"
		case IMPLIES(f1, f2) => "(" + FormulaToString(f1) + "-->" + FormulaToString(f2) + ")"
		case EXISTS(x1, f1) => "(exists " + x1 + " " + FormulaToString(f1) + ")"
		case FORALL(x1, f1) => "(forall " + x1 + " " + FormulaToString(f1) + ")"
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

	predicate WellFormedUniversalQuantifier(str: string)
		decreases |str|, 1
	{
		|str| > 11 && str[0] == '(' && "forall " <= str[1..] && str[|str|-1] == ')' &&
		var str1 := str[|"(forall "|..];
		' ' in str1 &&
		var var_name := ScanBoundVariableName(str1);
		ValidVariableName(var_name) &&
		var str2 := str1[|var_name|+1..|str1|-1];
		WellFormedFormula(str2)
	}

	predicate WellFormedExistentialQuantifier(str: string)
		decreases |str|, 1
	{
		|str| > 11 && str[0] == '(' && "exists " <= str[1..] && str[|str|-1] == ')' &&
		var str1 := str[|"(exists "|..];
		' ' in str1 &&
		var var_name := ScanBoundVariableName(str1);
		ValidVariableName(var_name) &&
		var str2 := str1[|var_name|+1..|str1|-1];
		WellFormedFormula(str2)
	}

	predicate WellFormedFormula(str: string)
		decreases |str|, 2
	{
		WellFormedAtomicFormula(str) || WellFormedNegation(str) || WellFormedConjunction(str) ||
		WellFormedDisjunction(str) || WellFormedImplication(str) ||
		WellFormedUniversalQuantifier(str) || WellFormedExistentialQuantifier(str)
	}

	function FirstIndexOf(c: char, str: string): nat
		requires c in str
		decreases |str|
	{
		if c == str[0] then 0 else assert |str| > 1 && c in str[1..]; 1+FirstIndexOf(c, str[1..])
	}

	lemma FirstIndexInString(str: string, i: nat)
		requires ' ' in str
		requires i == FirstIndexOf(' ', str)
		ensures i < |str| && str[i] == ' '
		decreases |str|
	{
		var c := ' ';
		if c == str[0] {}
		else { assert |str| > 1 && c in str[1..]; assert i > 0; FirstIndexInString(str[1..], i-1); }
	}
	
	function ScanBoundVariableName(str: string): string
		requires ' ' in str
	{
		var i := FirstIndexOf(' ', str);
		assert 0 <= i < |str| && str[i] == ' ' by { FirstIndexInString(str, i); }
		str[..i]
	}
/*
	// a simple parser, assuming full parentheses:
	function {:verify false} FormulaFromString(str: string): Formula
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
		else if WellFormedImplication(str) then
			var connective_index := BinaryConnectiveIndex(str, 1, 0);
			IMPLIES(FormulaFromString(str[1..connective_index]), FormulaFromString(str[connective_index+3..|str|-1]))
		else if WellFormedUniversalQuantifier(str) then
			var var_name := ScanBoundVariableName(str[|"(forall "|..]);
			FORALL(var_name, FormulaFromString(str[|"(forall " + var_name + " "|..|str|-1]))
		else
			assert WellFormedExistentialQuantifier(str);
			var var_name := ScanBoundVariableName(str[|"(exists "|..]);
			EXISTS(var_name, FormulaFromString(str[|"(exists " + var_name + " "|..|str|-1]))
	}
*/
	const p := VAR("p")
	const q := VAR("q")
	const r := VAR("r")
	const s := VAR("s")
	//const t := VAR("t")
	const A := VAR("A")
	const B := VAR("B")
	const C := VAR("C")
	const p1 := VAR("p1")
	const p2 := VAR("p2")
	const p3 := VAR("p3")
	const p4 := VAR("p4")
	const p5 := VAR("p5")
	const x := VAR("x")
	const y := VAR("y")
	const z := VAR("z")

	method Main'() {
		var f1 := FORALL("p", NOT(OR(P("P1",[p]), P("P2",[p, F("f", [q,p])]))));
		if !ValidFormula(f1) { return; }
		var str1 := FormulaToString(f1); // (r-->(¬(p\/q)))
		print str1, "\n";
//		if !WellFormedFormula(str1) { return; }
//		var f1' := FormulaFromString(str1);
//		if !ValidFormula(f1') { return; }
//		print FormulaToString(f1'), "\n";
	}
}