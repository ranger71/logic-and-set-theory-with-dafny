include "../propositional_logic.dfy"
include "../truth_tables.dfy"
include "../natural_deduction.dfy"

/*

Logic and Set Theory - lecture 7

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ Truth values, valuation/model of a formula
∙ Semantic entailment
∙ Soundness Propositional Logic
∙ Implication of soundnes: the non-existence of a proof for a given sequent <== a counterexample
∙ Tautologies (= validity of a formula, = always true), satisfiability (= not always false), satisfying assignments
∙ Natural deduction in Dafny

Today:
∙ Completeness of Propositional Logic
∙ Semantic equivalence; step-by-step proof by calculation in Dafny
∙ "Debugging" proofs (of natural deduction) in Dafny
∙ Introduction to predicate logic


1.4.4 Completeness of propositional logic

The natural deduction rules of propositional logic are complete: whenever
φ₁, φ₂, ... , φₙ ⊨ ψ holds, then there exists a natural deduction proof for the
sequent φ₁, φ₂, ... , φₙ ⊦ ψ.

Definition 1.36 (Tautology) A formula of propositional logic φ is called a tautology
iff it evaluates to T under all its valuations, i.e. iff ⊨ φ.

Theorem 1.37 If ⊨ η holds, then ⊦ η is valid. In other words, if η is a
tautology, then η is a theorem.

Corollary 1.39 (Soundness and Completeness) Let φ₁, φ₂, ... , φₙ, ψ
be formulas of propositional logic. Then

				φ₁, φ₂, ... , φₙ ⊨ ψ holds
		iff
				φ₁, φ₂, ... , φₙ ⊦ ψ is valid.


Some further extras from the Normal Forms section (1.5):

Definition 1.40 Let φ and ψ be formulas of propositional logic. We say
that φ and ψ are semantically equivalent iff φ ⊨ ψ and ψ ⊨ φ hold. In that
case we write φ ≡ ψ. Further, we call φ valid if ⊨ φ holds.


Definition 1.44 Given a formula φ in propositional logic, we say that φ is
satisfiable if it has a valuation in which is evaluates to T.

Proposition 1.45 Let φ be a formula of propositional logic. Then φ is satisfiable
iff ¬φ is not valid.


2 Predicate logic

2.1 The need for a richer language

	Every student is younger than some instructor.                       (2.1)

	S(x) : x is a student
	I(x) : x is an instructor
	Y (x, y) : x is younger than y.

	I(y) : y is an instructor

	I(z) : z is an instructor.

	∀x (S(x) ⟶ (∃y (I(y) ∧ Y(x, y))))

Another example: "Not all birds can fly."

	B(x) : x is a bird
	F(x) : x can fly

	¬(∀x (B(x) ⟶ F(x)))

	∃x (B(x) ∧ ¬F(x))

Our main objective is to reason symbolically (⊢) or
semantically (⊨) about the information expressed in those formulas.

Like in propositional logic, natural deduction for predicate logic is
sound and complete with respect to semantic entailment:

	φ₁, φ₂, ... , φₙ ⊦ ψ   iff   φ₁, φ₂, ... , φₙ ⊨ ψ

for formulas of the predicate calculus.


	No books are gaseous.
	Dictionaries are books.
	Therefore, no dictionary is gaseous."


	B(x) : x is a book
	G(x) : x is gaseous
	D(x) : x is a dictionary


	¬∃x (B(x) ∧ G(x)), ∀x (D(x) ⟶ B(x)) ⊦ ¬∃x (D(x) ∧ G(x))
	¬∃x (B(x) ∧ G(x)), ∀x (D(x) ⟶ B(x)) ⊨ ¬∃x (D(x) ∧ G(x))

Predicate logic extends propositional logic not only with quantifiers but
with one more concept, that of function symbols. Consider the declarative
sentence

	Every child is younger than its mother

	∀x ∀y (C(x) ∧ M(y, x) ⟶ Y (x, y))

where C(x) means that x is a child, M(x, y) means that x is y’s mother
and Y (x, y) means that x is younger than y.

	Andy and Paul have the same maternal grandmother.

	∀x ∀y ∀u ∀v (M(x, y) ∧ M(y, a) ∧ M(u, v) ∧ M(v, p) ⟶ x = u)

	∀x (C(x) ⟶ Y (x,m(x)))

	m(m(a)) = m(m(p))

	‘Ann likes Mary’s brother’ is ambiguous.
	
It might be that Ann likes one of Mary’s brothers, which we would write as

	∃x (B(x,m) ∧ L(a, x))

where B and L mean ‘is brother of’ and ‘likes,’ and a and m mean Ann and Mary.

	∀x (B(x,m) ⟶ L(a, x))

saying that any x which is a brother of Mary is liked by Ann. Predicates
should be used if a ‘function’ such as ‘your youngest brother’ does not always
have a value.

*/

module Logic_07 {
	import opened PropositionalLogic
	import opened TruthTables
	import opened NaturalDeduction

	// Semantic equivalence - example of step-by-step proof by calculation in Dafny:
	// negation of disjunction is the conjunction of the negations
	lemma DeMorgan_not_and_is_or_of_nots(f1: PropositionalFormula, f2: PropositionalFormula, assignment: map<string, bool>)
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
		== // by the three truth tables: of NOT, of OR, and of AND (in every one of the four rows)
			TruthTable_AND[(TruthTable_NOT[P1], TruthTable_NOT[P2])];
		==
			TruthTable_AND[(Value(NOT(f1), assignment), Value(NOT(f2), assignment))];
		==
			Value(AND(NOT(f1), NOT(f2)), assignment);
		}
	}

	// last exercise from assignment 1:
	// p ∧ q ⟶ r ⊢ (p ⟶ r) ∨ (q ⟶ r)
	const sequent_1_2_3m := ([IMPLIES(AND(p, q), r)], OR(IMPLIES(p, r), IMPLIES(q, r)))

	function Box_3m_Case_r(): Box {
		// case (a): when "r" holds it is implied by anything
		var Step3 := (r, Assumption);

		var Step4 := (p, Assumption);
		var Step5 := (r, Copy(Step3));
		var Box_4_5 := (Step4.0, Step5);
		var Step6 := (IMPLIES(p, r), IMPLIES_Introduction(Box_4_5));
		var Step7 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Introduction_1(Step6));
		
		(Step3.0, Step7)
	}

	function Box_3m_Case_not_r_p_q(): Box {
		var Recall_Step1 := (IMPLIES(AND(p, q), r), Premise); // recalling
		var Recall_Step8 := (NOT(r), Assumption);
		var Recall_Step10 := (p, Assumption);

		// case (b_1_a): the negation of "r" holds; "p" holds; when "q" holds too, "r" is implied in contradiction with the "not r"
		var Step12 := (q, Assumption);
		
		var Step13 := (AND(p, q), AND_Introduction(Recall_Step10, Step12));
		var Step14 := (r, IMPLIES_Elimination(Step13, Recall_Step1));
		var Step15 := (FALSE, NOT_Elimination(Step14, Recall_Step8));
		var Step16 := (OR(IMPLIES(p, r), IMPLIES(q, r)), Bottom_Elimination(Step15));
		
		(Step12.0, Step16)
	}

	function Box_3m_Case_not_r_p_not_q(): Box {
		// case (b_1_b): the negation of "r" holds; "p" holds; when the negation of "q" holds, "q" implies anything (including "r")
		var Step17 := (NOT(q), Assumption);

		var Step18 := (q, Assumption);
		var Step19 := (FALSE, NOT_Elimination(Step18, Step17));
		var Step20 := (r, Bottom_Elimination(Step19));
		var Box_18_20 := (Step18.0, Step20);

		var Step21 := (IMPLIES(q, r), IMPLIES_Introduction(Box_18_20));
		var Step22 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Introduction_2(Step21));
		
		(Step17.0, Step22)
	}

	function Box_3m_Case_not_r_p(): Box {
		var Step10 := (p, Assumption);

		// case (b_1): the negation of "r" holds; when "p" holds we have to consider "q" too
		var Step11 := (OR(q, NOT(q)), LEM);
		var Box_12_16 := Box_3m_Case_not_r_p_q();
		var Box_17_22 := Box_3m_Case_not_r_p_not_q();
		var Step23 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Elimination(Step11, Box_12_16, Box_17_22));

		(Step10.0, Step23)
	}

	function Box_3m_Case_not_r_not_p(): Box {
		var Recall_Step8 := (NOT(r), Assumption);

		// case (b_2): the negation of "r" holds; when the negation of "p" holds, "p" implies anything (including "r")
		var Step24 := (NOT(p), Assumption);

		var Step25 := (p, Assumption);
		var Step26 := (FALSE, NOT_Elimination(Step25, Step24));
		var Step27 := (r, Bottom_Elimination(Step26));
		var Box_25_27 := (Step25.0, Step27);

		var Step28 := (IMPLIES(p, r), IMPLIES_Introduction(Box_25_27));
		var Step29 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Introduction_1(Step28));
		
		(Step24.0, Step29)
	}

	function Box_3m_Case_not_r(): Box {
		// case (b): when the negation of "r" holds we have to consider further cases; let's start with "p"
		var Step8 := (NOT(r), Assumption);

		var Step9 := (OR(p, NOT(p)), LEM);
		var Box_10_23 := Box_3m_Case_not_r_p();
		var Box_24_29 := Box_3m_Case_not_r_not_p();
		var Step30 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Elimination(Step9, Box_10_23, Box_24_29));

		(Step8.0, Step30)
	}

	method ProofOfSequent_1_2_3m() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_3m, proof)
	{
		var Step1 := (IMPLIES(AND(p, q), r), Premise);
		var Step2 := (OR(r, NOT(r)), LEM);
		var Box_3_7 := Box_3m_Case_r();
		var Box_8_30 := Box_3m_Case_not_r();
		var Step31 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Elimination(Step2, Box_3_7, Box_8_30));
		assert CorrectProofStep(Step31, sequent_1_2_3m.0, []);
		proof := Step31;
	}

	method Main() {
		// last exercise from assignment 1
		var proof_sequent_1_2_3m := ProofOfSequent_1_2_3m();
		print "Section 1.2 optional Exercise 3(m): let sequent_1_2_3m be ";
		PrintSequent(sequent_1_2_3m);
		print "\nValidity proof for sequent_1_2_3m: \n";
		PrintSequentProof(sequent_1_2_3m, proof_sequent_1_2_3m);
	}
}