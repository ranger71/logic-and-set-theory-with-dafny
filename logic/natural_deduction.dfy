include "propositional_logic.dfy"

module NaturalDeduction {
	import opened PropositionalLogic

	type Sequent = (seq<PropositionalFormula>, PropositionalFormula)

	datatype NaturalDeductionStepJustification =
		Premise |
		AND_Introduction(NaturalDeductionStep, NaturalDeductionStep) |
		AND_Elimination_1(NaturalDeductionStep) |
		AND_Elimination_2(NaturalDeductionStep) |
		Double_Negation_Introduction(NaturalDeductionStep) |
		Double_Negation_Elimination(NaturalDeductionStep) |
		IMPLIES_Elimination(NaturalDeductionStep, NaturalDeductionStep) |
		MT(NaturalDeductionStep, NaturalDeductionStep) |
		Assumption |
		Copy(NaturalDeductionStep) |
		IMPLIES_Introduction(Box) |
		OR_Introduction_1(NaturalDeductionStep) |
		OR_Introduction_2(NaturalDeductionStep) |
		OR_Elimination(P: NaturalDeductionStep, box1: Box, box2: Box) |
		Bottom_Elimination(NaturalDeductionStep) |
		NOT_Elimination(NaturalDeductionStep, NaturalDeductionStep) |
		NOT_Introduction(Box) |
		PBC(Box) |
		LEM

	type NaturalDeductionStep = (PropositionalFormula, NaturalDeductionStepJustification)

	type Box = (PropositionalFormula, NaturalDeductionStep) // assumption + proof

	// define SequentProof as a tree of steps (instead of as a sequence + nested boxes in the textbook);
	// a SequentProof is defined as a NaturalDeductionStep with a validity predicate,
	// ensuring that only premises of the given sequent are used;
	// pretty-print of such a tree as a sequence makes it look like proofs in the book,
	// with the premises listed first, boxes highlighted, and avoiding unnecessary duplication
	type SequentProof = NaturalDeductionStep

	ghost predicate ValidSequent(s: Sequent) { forall p | p in s.0 || p == s.1 :: ValidFormula(p) }
	ghost predicate CorrectSequent(s: Sequent) { exists proof :: CorrectSequentProof(s, proof) }
	ghost predicate CorrectSequentProof(s: Sequent, proof: SequentProof) {
		ValidSequent(s) &&
		ValidFormula(proof.0) &&
		ValidStep(proof) &&
		proof.0 == s.1 && // the expected conclusion
		CorrectProofStep(proof, s.0, [])
	}
	ghost predicate ValidStep(step: NaturalDeductionStep)
		decreases step, 1
	{
		ValidFormula(step.0) &&
		match step.1
		case Premise => true
		case AND_Introduction(L, R) => ValidStep(L) && ValidStep(R)
		case AND_Elimination_1(P) => ValidStep(P)
		case AND_Elimination_2(P) => ValidStep(P)
		case Double_Negation_Introduction(P) => ValidStep(P)
		case Double_Negation_Elimination(P) => ValidStep(P)
		case IMPLIES_Elimination(L, R) => ValidStep(L) && ValidStep(R)
		case MT(L, R) => ValidStep(L) && ValidStep(R)
		case Assumption => true
		case Copy(P) => ValidStep(P)
		case IMPLIES_Introduction(box) => ValidFormula(box.0) && ValidStep(box.1)
		case OR_Introduction_1(P) => ValidStep(P)
		case OR_Introduction_2(P) => ValidStep(P)
		case OR_Elimination(P, box1, box2) => ValidStep(P) && ValidFormula(box1.0) && ValidStep(box1.1) && ValidFormula(box2.0) && ValidStep(box2.1)
		case Bottom_Elimination(P) => ValidStep(P)
		case NOT_Elimination(L, R) => ValidStep(L) && ValidStep(R)
		case NOT_Introduction(box) => ValidFormula(box.0) && ValidStep(box.1)
		case PBC(box) => ValidFormula(box.0) && ValidStep(box.1)
		case LEM => true
	}

	ghost predicate CorrectProofStep(step: NaturalDeductionStep, premises: seq<PropositionalFormula>, assumptions: seq<PropositionalFormula>)
		requires ValidStep(step)
		requires forall f | f in premises || f in assumptions :: ValidFormula(f)
		decreases step
	{
		match step.1
		case Premise =>
			step.0 in premises
		case AND_Introduction(L, R) =>
			step.0 == AND(L.0, R.0) &&
			CorrectProofStep(L, premises, assumptions) &&
			CorrectProofStep(R, premises, assumptions)
		case AND_Elimination_1(P) =>
			P.0.AND? &&
			P.0.L == step.0 &&
			CorrectProofStep(P, premises, assumptions)
		case AND_Elimination_2(P) =>
			P.0.AND? &&
			P.0.R == step.0 &&
			CorrectProofStep(P, premises, assumptions)
		case Double_Negation_Introduction(P) =>
			step.0 == NOT(NOT(P.0)) &&
			CorrectProofStep(P, premises, assumptions)
		case Double_Negation_Elimination(P) =>
			P.0 == NOT(NOT(step.0)) &&
			CorrectProofStep(P, premises, assumptions)
		case IMPLIES_Elimination(L, R) =>
			R.0 == IMPLIES(L.0, step.0) &&
			CorrectProofStep(L, premises, assumptions) &&
			CorrectProofStep(R, premises, assumptions)
		case MT(L, R) =>
			L.0.IMPLIES? &&
			R.0.NOT? &&
			step.0.NOT? &&
			L.0 == IMPLIES(step.0.P, R.0.P) &&
			CorrectProofStep(L, premises, assumptions) &&
			CorrectProofStep(R, premises, assumptions)
		case Assumption =>
			step.0 in assumptions
		case Copy(P) =>
			step.0 == P.0 &&
			CorrectProofStep(P, premises, assumptions)
		case IMPLIES_Introduction(box) =>
			step.0 == IMPLIES(box.0, box.1.0) &&
			CorrectProofStep(box.1, premises, assumptions + [box.0])
		case OR_Introduction_1(P) =>
			step.0.OR? && step.0.L == P.0 &&
			CorrectProofStep(P, premises, assumptions)
		case OR_Introduction_2(P) =>
			step.0.OR? &&
			step.0.R == P.0 &&
			CorrectProofStep(P, premises, assumptions)
		case OR_Elimination(P, box1, box2) =>
			P.0.OR? &&
			CorrectProofStep(P, premises, assumptions) &&
			step.0 == box1.1.0 == box2.1.0 &&
			P.0.L == box1.0 &&
			P.0.R == box2.0 &&
			CorrectProofStep(box1.1, premises, assumptions + [box1.0]) &&
			CorrectProofStep(box2.1, premises, assumptions + [box2.0])
		case Bottom_Elimination(P) =>
			P.0 == FALSE &&
			CorrectProofStep(P, premises, assumptions)
		case NOT_Elimination(L, R) =>
			step.0 == FALSE &&
			NOT(L.0) == R.0 &&
			CorrectProofStep(L, premises, assumptions) &&
			CorrectProofStep(R, premises, assumptions)
		case NOT_Introduction(box) =>
			step.0 == NOT(box.0) &&
			box.1.0 == FALSE &&
			CorrectProofStep(box.1, premises, assumptions + [box.0])
		case PBC(box) =>
			box.0 == NOT(step.0) &&
			box.1.0 == FALSE &&
			CorrectProofStep(box.1, premises, assumptions + [box.0])
		case LEM =>
			step.0.OR? &&
			NOT(step.0.L) == step.0.R
	}

	method PrintSequent(s: Sequent)
		requires ValidSequent(s)
	{
		if |s.0| > 0 {
			print FormulaToString(s.0[0]);
			var i := 1;
			while i < |s.0|
				invariant 1 <= i <= |s.0|
			{
				print ", ", FormulaToString(s.0[i]);
				i := i + 1;
			}
			print " ";
		}
		print "|- ", FormulaToString(s.1), "\n";
	}

	function RepeatChar(c: char, n: nat): string
		decreases n
	{
		if n == 0 then "" else [c] + RepeatChar(c, n-1)
	}

	function Indentation(n: nat): string { RepeatChar(' ', n) }

	function Max2(x: nat, y: nat): nat { if x >= y then x else y }

	function DeepestBoxNesting(step: NaturalDeductionStep): nat
		requires ValidStep(step)
	{
		match step.1
		case Premise => 0
		case AND_Introduction(L, R) => Max2(DeepestBoxNesting(L), DeepestBoxNesting(R))
		case AND_Elimination_1(P) => DeepestBoxNesting(P)
		case AND_Elimination_2(P) => DeepestBoxNesting(P)
		case Double_Negation_Introduction(P) => DeepestBoxNesting(P)
		case Double_Negation_Elimination(P) => DeepestBoxNesting(P)
		case IMPLIES_Elimination(L, R) => Max2(DeepestBoxNesting(L), DeepestBoxNesting(R))
		case MT(L, R) => Max2(DeepestBoxNesting(L), DeepestBoxNesting(R))
		case Assumption => 0
		case Copy(P) => DeepestBoxNesting(P)
		case IMPLIES_Introduction(box) => 1 + DeepestBoxNesting(box.1)
		case OR_Introduction_1(P) => DeepestBoxNesting(P)
		case OR_Introduction_2(P) => DeepestBoxNesting(P)
		case OR_Elimination(P, box1, box2) => 1 + Max2(DeepestBoxNesting(box1.1), DeepestBoxNesting(box2.1))
		case Bottom_Elimination(P) => DeepestBoxNesting(P)
		case NOT_Elimination(L, R) => Max2(DeepestBoxNesting(L), DeepestBoxNesting(R))
		case NOT_Introduction(box) => 1 + DeepestBoxNesting(box.1)
		case PBC(box) => 1 + DeepestBoxNesting(box.1)
		case LEM => 0
	}

	method {:verify false} PrintProofStep(step: NaturalDeductionStep, i0: nat, visible0: map<PropositionalFormula, nat>, justification_column: nat, depth: nat, deepest_nesting: nat) returns (i: nat, visible: map<PropositionalFormula, nat>)
		requires ValidStep(step)
		requires depth <= deepest_nesting
		ensures step.0 in visible.Keys
		decreases step
	{
		i, visible := i0, visible0;
		if step.0 in visible.Keys && !step.1.Copy? { return; }
		match step.1 {
		case Premise =>
			print ProofLine(i, step.0, "premise", justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		case AND_Introduction(L, R) => {
			i, visible := PrintProofStep(L, i, visible, justification_column, depth, deepest_nesting);
			i, visible := PrintProofStep(R, i, visible, justification_column, depth, deepest_nesting);
			var justification := "/\\i " + DecimalAsString(visible[L.0]) + "," + DecimalAsString(visible[R.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case AND_Elimination_1(P) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var justification := "/\\e1 " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case AND_Elimination_2(P) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var justification := "/\\e2 " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case Double_Negation_Introduction(P) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var justification := "¬¬i " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case Double_Negation_Elimination(P) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var justification := "¬¬e " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case IMPLIES_Elimination(L, R) => {
			i, visible := PrintProofStep(L, i, visible, justification_column, depth, deepest_nesting);
			i, visible := PrintProofStep(R, i, visible, justification_column, depth, deepest_nesting);
			var justification := "-->e " + DecimalAsString(visible[L.0]) + "," + DecimalAsString(visible[R.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case MT(L, R) => {
			i, visible := PrintProofStep(L, i, visible, justification_column, depth, deepest_nesting);
			i, visible := PrintProofStep(R, i, visible, justification_column, depth, deepest_nesting);
			var justification := "MT " + DecimalAsString(visible[L.0]) + "," + DecimalAsString(visible[R.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case Assumption =>
			print ProofLine(i, step.0, "assumption", justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		case Copy(P) => {
			var justification := "copy " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			// redundant yet harmless map update (as the Copy step it is likely to end a box and the mapping is local to that box)
			i, visible := i+1, visible[step.0 := i];
		}
		case IMPLIES_Introduction(box) => {
			var visible1 := visible[box.0 := i];
			var line := RepeatChar('─', justification_column - 2*depth + 25);
			print RepeatChar('│', depth), "┌", line, "┐", RepeatChar('│', depth), "\n";
			print ProofLine(i, box.0, "assumption", justification_column, depth+1, deepest_nesting);
			i, visible1 := PrintProofStep(box.1, i+1, visible1, justification_column, depth+1, deepest_nesting);
			print RepeatChar('│', depth), "└", line, "┘", RepeatChar('│', depth), "\n";
			var justification := "-->i " + DecimalAsString(i0) + "-" + DecimalAsString(i-1);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case OR_Introduction_1(P) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var justification := "\\/i1 " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case OR_Introduction_2(P) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var justification := "\\/i2 " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case OR_Elimination(P, box1, box2) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var i1, visible1 := i, visible[box1.0 := i];
			var line := RepeatChar('─', justification_column - 2*depth + 25);
			print RepeatChar('│', depth), "┌", line, "┐", RepeatChar('│', depth), "\n";
			print ProofLine(i, box1.0, "assumption", justification_column, depth+1, deepest_nesting);
			i, visible1 := PrintProofStep(box1.1, i+1, visible1, justification_column, depth+1, deepest_nesting);
			print RepeatChar('│', depth), "└", line, "┘", RepeatChar('│', depth), "\n";
			var i2, visible2 := i, visible[box2.0 := i];
			print RepeatChar('│', depth), "┌", line, "┐", RepeatChar('│', depth), "\n";
			print ProofLine(i, box2.0, "assumption", justification_column, depth+1, deepest_nesting);
			i, visible2 := PrintProofStep(box2.1, i+1, visible2, justification_column, depth+1, deepest_nesting);
			print RepeatChar('│', depth), "└", line, "┘", RepeatChar('│', depth), "\n";
			var justification := "\\/e " + DecimalAsString(visible[P.0]) + "," + DecimalAsString(i1) + "-" + DecimalAsString(i2-1) + "," + DecimalAsString(i2) + "-" + DecimalAsString(i-1);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case Bottom_Elimination(P) => {
			i, visible := PrintProofStep(P, i, visible, justification_column, depth, deepest_nesting);
			var justification := "Fe " + DecimalAsString(visible[P.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case NOT_Elimination(L, R) => {
			i, visible := PrintProofStep(L, i, visible, justification_column, depth, deepest_nesting);
			i, visible := PrintProofStep(R, i, visible, justification_column, depth, deepest_nesting);
			var justification := "¬e " + DecimalAsString(visible[L.0]) + "," + DecimalAsString(visible[R.0]);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case NOT_Introduction(box) => {
			var visible1 := visible[box.0 := i];
			var line := RepeatChar('─', justification_column - 2*depth + 25);
			print RepeatChar('│', depth), "┌", line, "┐", RepeatChar('│', depth), "\n";
			print ProofLine(i, box.0, "assumption", justification_column, depth+1, deepest_nesting);
			i, visible1 := PrintProofStep(box.1, i+1, visible1, justification_column, depth+1, deepest_nesting);
			print RepeatChar('│', depth), "└", line, "┘", RepeatChar('│', depth), "\n";
			var justification := "¬i " + DecimalAsString(i0) + "-" + DecimalAsString(i-1);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
		case PBC(box) =>
			var visible1 := visible[box.0 := i];
			var line := RepeatChar('─', justification_column - 2*depth + 25);
			print RepeatChar('│', depth), "┌", line, "┐", RepeatChar('│', depth), "\n";
			print ProofLine(i, box.0, "assumption", justification_column, depth+1, deepest_nesting);
			i, visible1 := PrintProofStep(box.1, i+1, visible1, justification_column, depth+1, deepest_nesting);
			print RepeatChar('│', depth), "└", line, "┘", RepeatChar('│', depth), "\n";
			var justification := "PBC " + DecimalAsString(i0) + "-" + DecimalAsString(i-1);
			print ProofLine(i, step.0, justification, justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		case LEM =>
			print ProofLine(i, step.0, "LEM", justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[step.0 := i];
		}
	}

	const DigitAsString := ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]

	function DecimalAsString(n: nat): string
		decreases n
	{
		if n < 10 then DigitAsString[n] else DecimalAsString(n/10) + DigitAsString[n%10]
	}

	function ProofLine(i: nat, f: PropositionalFormula, justification: string, justification_column: nat, depth: nat, deepest_nesting: nat): string
		requires ValidFormula(f)
		requires depth <= deepest_nesting
	{
		var i_str := DecimalAsString(i);
		var line_prefix1 := RepeatChar('│', depth) + Indentation(deepest_nesting-depth+4) + i_str;
		var n1 := deepest_nesting+12-|line_prefix1|;
		var line_prefix2 := line_prefix1 + Indentation(if n1 < 4 then 4 else n1);
		var f_str := FormulaToString(f);
		var line_prefix3 := line_prefix2 + f_str;
		var n2 := justification_column-|line_prefix3|;
		var line_prefix4 := line_prefix3 + Indentation(if n2 < 4 then 4 else n2) + justification;
		var n3 := justification_column + 27 - depth - |line_prefix4|;
		line_prefix4 + Indentation(if n3 < 1 then 1 else n3) + RepeatChar('│', depth) + "\n"
	}

	method PrintSequentProof'(s: Sequent, proof: SequentProof, justification_column: nat, deepest_nesting: nat)
		requires CorrectSequentProof(s, proof)
	{
		var i: nat, visible: map<PropositionalFormula, nat> := 1, map[];
		var depth := 0;
		while i != |s.0|+1
			invariant 1 <= i <= |s.0|+1
		{
			print ProofLine(i, s.0[i-1], "premise", justification_column, depth, deepest_nesting);
			i, visible := i+1, visible[s.0[i-1] := i];
		}
		i, visible := PrintProofStep(proof, i, visible, justification_column, depth, deepest_nesting);
		print "\n";
	}

	method PrintSequentProof(s: Sequent, proof: SequentProof)
		requires CorrectSequentProof(s, proof)
	{
		PrintSequentProof'(s, proof, 40, DeepestBoxNesting(proof));
	}
}