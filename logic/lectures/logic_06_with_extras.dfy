include "../propositional_logic.dfy"
include "../natural_deduction.dfy"

/*

Logic and Set Theory - lecture 6

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ The semantics of a propositional formula by Truth Tables

Today and (part of) next week:
∙ Truth values, valuation/model of a formula
∙ Semantic entailment
∙ Soundness and Completeness of Propositional Logic
∙ Implication of soundnes: the non-existence of a proof for a given sequent <== a counterexample
∙ Tautologies, satisfying assignments, logical equivalence
∙ Natural deduction in Dafny


Recalling Last week's definition of the semantics of a propositional formula
using truth tables (+ some the definition of truth values and a valuation/model):

Definition 1.28

1. The set of truth values contains two elements T and F, where
T represents ‘true’ and F represents ‘false’.

2. A valuation or model of a formula φ is an assignment of each propositional atom
in φ to a truth value.

See Figure 1.7 on Page 40 ("The evaluation of a logical formula under a given valuation.")
and Figure 1.8 on the same page ("An example of a truth table for a more complex logical formula.")

1.4.3 Soundness of propositional logic

Definition 1.34 If, for all valuations in which all φ₁, φ₂, ... , φₙ evaluate to T,
ψ evaluates to T as well, we say that

				φ₁, φ₂, ... , φₙ ⊨ ψ

holds and call ⊨ the "semantic entailment" relation.

Theorem 1.35 (Soundness) Let φ₁, φ₂, ... , φₙ and ψ be propositional logic formulas. 
If φ₁, φ₂, ... , φₙ ⊦ ψ is valid, then φ₁, φ₂, ... , φₙ ⊨ ψ holds.

The proof uses mathematical induction on the length of a natural deduction proof
that the conjunct is valid.


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

*/
module Logic_06 {
	import opened PropositionalLogic
	import opened NaturalDeduction

	// p /\ q, r |- q /\ r
	const sequent1 := ([AND(p, q), r], AND(q, r))

	method CorrectSequent1()
		ensures CorrectSequent(sequent1)
	{
		var proof_sequent1 := ProofOfSequent1();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent1, proof) by {
			assert CorrectSequentProof(sequent1, proof_sequent1);
		}
	}

	method ProofOfSequent1() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent1, proof)
	{
		var Step1, Step2, Step3, Step4;
		// proof by construction: at each step we add a proposition to the result sequence that's provable by earlier ones,
		// and the final proposition will be the sequent's RHS (conclusion)
		Step1 := (AND(p, q), Premise);
		Step2 := (r, Premise);
		Step3 := (q, AND_Elimination_2(Step1));
		Step4 := (AND(q, r), AND_Introduction(Step3, Step2));
		proof := Step4;
	}

	// p, not(not(q /\ r)) |- not(not(p)) /\ r
	const sequent_example_1_5 := ([p, NOT(NOT(AND(q, r)))], AND(NOT(NOT(p)), r))

	method CorrectSequent_1_5()
		ensures CorrectSequent(sequent_example_1_5)
	{
		var proof_example_1_5 := ProofOfSequent_example_1_5();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_1_5, proof) by {
			assert CorrectSequentProof(sequent_example_1_5, proof_example_1_5);
		}
	}

	method ProofOfSequent_example_1_5() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_1_5, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Step6;
		Step1 := (p, Premise);
		Step2 := (NOT(NOT(AND(q, r))), Premise);
		Step3 := (NOT(NOT(p)), Double_Negation_Introduction(Step1));
		Step4 := (AND(q, r), Double_Negation_Elimination(Step2));
		Step5 := (r, AND_Elimination_2(Step4));
		Step6 := (AND(NOT(NOT(p)), r), AND_Introduction(Step3, Step5));
		proof := Step6;
	}

	// p, p --> q, p --> (q --> r) |- r
	const sequent_example_page10 := ([p, IMPLIES(p, q), IMPLIES(p, IMPLIES(q, r))], r)

	method CorrectSequent_page10()
		ensures CorrectSequent(sequent_example_page10)
	{
		var proof := ProofOfSequent_example_page10();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_page10, proof) by {
			assert CorrectSequentProof(sequent_example_page10, proof);
		}
	}

	method ProofOfSequent_example_page10() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_page10, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Step6;
		Step1 := (IMPLIES(p, IMPLIES(q, r)), Premise);
		Step2 := (IMPLIES(p, q), Premise);
		Step3 := (p, Premise);
		Step4 := (IMPLIES(q, r), IMPLIES_Elimination(Step3, Step1));
		Step5 := (q, IMPLIES_Elimination(Step3, Step2));
		Step6 := (r, IMPLIES_Elimination(Step5, Step4));
		proof := Step6;
	}

	// p --> (q --> r), p, not(r) |- not(q)
	const sequent_example_1_7 := ([IMPLIES(p, IMPLIES(q, r)), p, NOT(r)], NOT(q))

	method CorrectSequent_1_7()
		ensures CorrectSequent(sequent_example_1_7)
	{
		var proof_example_1_7 := ProofOfSequent_example_1_7();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_1_7, proof) by {
			assert CorrectSequentProof(sequent_example_1_7, proof_example_1_7);
		}
	}

	method ProofOfSequent_example_1_7() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_1_7, proof)
	{
		var Step1, Step2, Step3, Step4, Step5;
		Step1 := (IMPLIES(p, IMPLIES(q, r)), Premise);
		Step2 := (p, Premise);
		Step3 := (NOT(r), Premise);
		Step4 := (IMPLIES(q, r), IMPLIES_Elimination(Step2, Step1));
		Step5 := (NOT(q), MT(Step4, Step3));
		proof := Step5;
		var s := sequent_example_1_7;
	}

	// p --> q |- not(q) --> not(p)
	const sequent_example_page11 := ([IMPLIES(p, q)], IMPLIES(NOT(q), NOT(p)))

	method CorrectSequent_page11()
		ensures CorrectSequent(sequent_example_page11)
	{
		var proof := ProofOfSequent_example_page11();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_page11, proof) by {
			assert CorrectSequentProof(sequent_example_page11, proof);
		}
	}

	method ProofOfSequent_example_page11() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_page11, proof)
	{
		var Step1, Step2, Step3, Step4, Box_2_3;
		Step1 := (IMPLIES(p, q), Premise);
		Step2 := (NOT(q), Assumption);
		Step3 := (NOT(p), MT(Step1, Step2));
		Box_2_3 := (Step2.0, Step3);
		Step4 := (IMPLIES(NOT(q), NOT(p)), IMPLIES_Introduction(Box_2_3));
		proof := Step4;
	}

	// not(q) --> not(p) |- p --> not(not(q))
	const sequent_example_1_9 := ([IMPLIES(NOT(q), NOT(p))], IMPLIES(p, NOT(NOT(q))))

	method CorrectSequent_1_9()
		ensures CorrectSequent(sequent_example_1_9)
	{
		var proof_example_1_9 := ProofOfSequent_example_1_9();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_1_9, proof) by {
			assert CorrectSequentProof(sequent_example_1_9, proof_example_1_9);
		}
	}

	method ProofOfSequent_example_1_9() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_1_9, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Box_2_4;
		Step1 := (IMPLIES(NOT(q), NOT(p)), Premise);
		Step2 := (p, Assumption);
		Step3 := (NOT(NOT(p)), Double_Negation_Introduction(Step2));
		Step4 := (NOT(NOT(q)), MT(Step1, Step3));
		Box_2_4 := (Step2.0, Step4);
		Step5 := (IMPLIES(p, NOT(NOT(q))), IMPLIES_Introduction(Box_2_4));
		proof := Step5;
	}

	// Definition 1.10 (page 13)
	ghost predicate IsTheorem(s: Sequent) { |s.0| == 0 }

	// |- (q --> r) --> ((not(q) --> not(p)) --> (p --> r))
	const sequent_example_1_11 := ([], IMPLIES(IMPLIES(q, r), IMPLIES(IMPLIES(NOT(q), NOT(p)), IMPLIES(p, r))))

	lemma Sequent_Example_1_11_Is_A_Theorem() ensures IsTheorem(sequent_example_1_11) {}

	method CorrectSequent_1_11()
		ensures CorrectSequent(sequent_example_1_11)
	{
		var proof_example_1_11 := ProofOfSequent_example_1_11();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_1_11, proof) by {
			assert CorrectSequentProof(sequent_example_1_11, proof_example_1_11);
		}
	}

	method ProofOfSequent_example_1_11() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_1_11, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Step6, Step7, Step8, Step9, Step10, Box_3_7, Box_2_8, Box_1_9;
		Step1 := (IMPLIES(q, r), Assumption);
		Step2 := (IMPLIES(NOT(q), NOT(p)), Assumption);
		Step3 := (p, Assumption);
		Step4 := (NOT(NOT(p)), Double_Negation_Introduction(Step3));
		Step5 := (NOT(NOT(q)), MT(Step2, Step4));
		Step6 := (q, Double_Negation_Elimination(Step5));
		Step7 := (r, IMPLIES_Elimination(Step6, Step1));
		Box_3_7 := (Step3.0, Step7);
		Step8 := (IMPLIES(p, r), IMPLIES_Introduction(Box_3_7));
		Box_2_8 := (Step2.0, Step8);
		Step9 := (IMPLIES(IMPLIES(NOT(q), NOT(p)), IMPLIES(p, r)), IMPLIES_Introduction(Box_2_8));
		Box_1_9 := (Step1.0, Step9);
		Step10 := (sequent_example_1_11.1, IMPLIES_Introduction(Box_1_9));
		proof := Step10;
	}

	// The rules for disjunction

	// p \/ q |- q \/ p
	const sequent_example_page17 := ([OR(p, q)], OR(q, p))

	method CorrectSequent_page17()
		ensures CorrectSequent(sequent_example_page17)
	{
		var proof := ProofOfSequent_example_page17();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_page17, proof) by {
			assert CorrectSequentProof(sequent_example_page17, proof);
		}
	}

	method ProofOfSequent_example_page17() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_page17, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Step6, Box_2_3, Box_4_5;
		Step1 := (OR(p, q), Premise);
		Step2 := (p, Assumption);
		Step3 := (OR(q, p), OR_Introduction_2(Step2));
		Box_2_3 := (Step2.0, Step3);
		Step4 := (q, Assumption);
		Step5 := (OR(q, p), OR_Introduction_1(Step4));
		Box_4_5 := (Step4.0, Step5);
		Step6 := (OR(q, p), OR_Elimination(Step1, Box_2_3, Box_4_5));
		proof := Step6;
	}

	// |- p --> (q --> p)
	const sequent_example_page20 := ([], IMPLIES(p, IMPLIES(q, p)))

	method CorrectSequent_page20()
		ensures CorrectSequent(sequent_example_page20)
	{
		var proof := ProofOfSequent_example_page20();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_page20, proof) by {
			assert CorrectSequentProof(sequent_example_page20, proof);
		}
	}

	method ProofOfSequent_example_page20() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_page20, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Box_2_3, Box_1_4;
		Step1 := (p, Assumption);
		Step2 := (q, Assumption);
		Step3 := (p, Copy(Step1));
		Box_2_3 := (Step2.0, Step3);
		Step4 := (IMPLIES(q, p), IMPLIES_Introduction(Box_2_3));
		Box_1_4 := (Step1.0, Step4);
		Step5 := (IMPLIES(p, IMPLIES(q, p)), IMPLIES_Introduction(Box_1_4));
		proof := Step5;
	}

	// contradictions: bottom elimination, not elimination
	// [0 := "p", 1 := "q", 2 := "r"]
	// not(p) \/ q |- p --> q
	const sequent_example_1_20 := ([OR(NOT(p), q)], IMPLIES(p, q))

	method CorrectSequent_1_20()
		ensures CorrectSequent(sequent_example_1_20)
	{
		var proof_example_1_20 := ProofOfSequent_example_1_20();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_1_20, proof) by {
			assert CorrectSequentProof(sequent_example_1_20, proof_example_1_20);
		}
	}

	method ProofOfSequent_example_1_20() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_1_20, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Step6, Step7, Step8, Step9, Step10, Step11;
		var Box_2_6, Box_3_5, Box_7_10, Box_8_9;
		Step1 := (OR(NOT(p), q), Premise);
		Step2 := (NOT(p), Assumption);
		Step3 := (p, Assumption);
		Step4 := (FALSE, NOT_Elimination(Step3, Step2));
		Step5 := (q, Bottom_Elimination(Step4));
		Box_3_5 := (Step3.0, Step5);
		Step6 := (IMPLIES(p, q), IMPLIES_Introduction(Box_3_5));
		Box_2_6 := (Step2.0, Step6);
		Step7 := (q, Assumption);
		Step8 := (p, Assumption);
		Step9 := (q, Copy(Step7));
		Box_8_9 := (Step8.0, Step9);
		Step10 := (IMPLIES(p, q), IMPLIES_Introduction(Box_8_9));
		Box_7_10 := (Step7.0, Step10);
		Step11 := (IMPLIES(p, q), OR_Elimination(Step1, Box_2_6, Box_7_10));
		proof := Step11;
	}

	// p --> q, p --> not(q) |- not(p)
	const sequent_example_1_21 := ([IMPLIES(p, q), IMPLIES(p, NOT(q))], NOT(p))

	method CorrectSequent_1_21()
		ensures CorrectSequent(sequent_example_1_21)
	{
		var proof_example_1_21 := ProofOfSequent_example_1_21();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_example_1_21, proof) by {
			assert CorrectSequentProof(sequent_example_1_21, proof_example_1_21);
		}
	}

	method ProofOfSequent_example_1_21() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_example_1_21, proof)
	{
		var Step1, Step2, Step3, Step4, Step5, Step6, Step7, Box_3_6;
		Step1 := (IMPLIES(p, q), Premise);
		Step2 := (IMPLIES(p, NOT(q)), Premise);
		Step3 := (p, Assumption);
		Step4 := (q, IMPLIES_Elimination(Step3, Step1));
		Step5 := (NOT(q), IMPLIES_Elimination(Step3, Step2));
		Step6 := (FALSE, NOT_Elimination(Step4, Step5));
		Box_3_6 := (Step3.0, Step6);
		Step7 := (NOT(p), NOT_Introduction(Box_3_6));
		proof := Step7;
	}

	method Main() {
		var proof_sequent_1 := ProofOfSequent1();
		print "sequent1: ";
		PrintSequent(sequent1);
		print "\nValidity proof for sequent1: \n";
		PrintSequentProof(sequent1, proof_sequent_1);
		/*
		sequent1: (p/\q), r |- (q/\r)

		Validity proof for sequent1: 
			1       (p/\q)                      premise
			2       r                           premise
			3       q                           /\e2 1
			4       (q/\r)                      /\i 3,2
		*/
		
		var proof_sequent_example_1_5 := ProofOfSequent_example_1_5();
		print "sequent_example_1_5: ";
		PrintSequent(sequent_example_1_5);
		print "\nValidity proof for sequent_example_1_5: \n";
		PrintSequentProof(sequent_example_1_5, proof_sequent_example_1_5);
		/*
		sequent_example_1_5: p, (¬(¬(q/\r))) |- ((¬(¬p))/\r)

		Validity proof for sequent_example_1_5: 
			1       p                           premise
			2       (¬(¬(q/\r)))                premise
			3       (¬(¬p))                     ¬¬i 1
			4       (q/\r)                      ¬¬e 2
			5       r                           /\e2 4
			6       ((¬(¬p))/\r)                /\i 3,5
		*/

		var proof_sequent_example_page10 := ProofOfSequent_example_page10();
		print "sequent_example_page10: ";
		PrintSequent(sequent_example_page10);
		print "\nValidity proof for sequent_example_page10: \n";
		PrintSequentProof(sequent_example_page10, proof_sequent_example_page10);
		/*
		sequent_example_page10: p, (p-->q), (p-->(q-->r)) |- r

		Validity proof for sequent_example_page10:
			1       p                           premise
			2       (p-->q)                     premise
			3       (p-->(q-->r))               premise
			4       q                           -->e 1,2
			5       (q-->r)                     -->e 1,3
			6       r                           -->e 4,5
		*/

		var proof_sequent_example_1_7 := ProofOfSequent_example_1_7();
		print "sequent_example_1_7: ";
		PrintSequent(sequent_example_1_7);
		print "\nValidity proof for sequent_example_1_7: \n";
		PrintSequentProof(sequent_example_1_7, proof_sequent_example_1_7);
		/*
		sequent_example_1_7: (p-->(q-->r)), p, (¬r) |- (¬q)

		Validity proof for sequent_example_1_7: 
			1       (p-->(q-->r))               premise
			2       p                           premise
			3       (¬r)                        premise
			4       (q-->r)                     -->e 2,1                   
			5       (¬q)                        MT 4,3
		*/

		var proof_sequent_example_page11 := ProofOfSequent_example_page11();
		print "sequent_example_page11: ";
		PrintSequent(sequent_example_page11);
		print "\nValidity proof for sequent_example_page11: \n";
		PrintSequentProof(sequent_example_page11, proof_sequent_example_page11);		
		/*
		sequent_example_page11: (p-->q) |- ((¬q)-->(¬p))

		Validity proof for sequent_example_page11:
			1       (p-->q)                    premise
		┌─────────────────────────────────────────────────────────────────┐
		│    2       (¬q)                       assumption                │
		│    3       (¬p)                       MT 1,2                    │
		└─────────────────────────────────────────────────────────────────┘
			4       ((¬q)-->(¬p))              -->i 2-3
		*/

		var proof_sequent_example_1_9 := ProofOfSequent_example_1_9();
		print "sequent_example_1_9: ";
		PrintSequent(sequent_example_1_9);
		print "\nValidity proof for sequent_example_1_9: \n";
		PrintSequentProof(sequent_example_1_9, proof_sequent_example_1_9);
		/*
		sequent_example_1_9: ((¬q)-->(¬p)) |- (p-->(¬(¬q)))

		Validity proof for sequent_example_1_9: 
			1       ((¬q)-->(¬p))              premise
		┌─────────────────────────────────────────────────────────────────┐
		│    2       p                          assumption                │
		│    3       (¬(¬p))                    ¬¬i 2                     │
		│    4       (¬(¬q))                    MT 1,3                    │
		└─────────────────────────────────────────────────────────────────┘
			5       (p-->(¬(¬q)))              -->i 2-4
		*/

		var proof_sequent_example_1_11 := ProofOfSequent_example_1_11();
		print "sequent_example_1_11: ";
		PrintSequent(sequent_example_1_11);
		print "\nValidity proof for sequent_example_1_11: \n";
		PrintSequentProof(sequent_example_1_11, proof_sequent_example_1_11);
		/*
		sequent_example_1_11: |- ((q-->r)-->(((¬q)-->(¬p))-->(p-->r)))

		Validity proof for sequent_example_1_11: 
		┌─────────────────────────────────────────────────────────────────┐
		│      1       (q-->r)                  assumption                │
		│┌───────────────────────────────────────────────────────────────┐│
		││     2       ((¬q)-->(¬p))            assumption               ││
		││┌─────────────────────────────────────────────────────────────┐││
		│││    3       p                        assumption              │││
		│││    4       (¬(¬p))                  ¬¬i 3                   │││
		│││    5       (¬(¬q))                  MT 2,4                  │││
		│││    6       q                        ¬¬e 5                   │││
		│││    7       r                        -->e 6,1                │││
		││└─────────────────────────────────────────────────────────────┘││
		││     8       (p-->r)                  -->i 3-7                 ││
		│└───────────────────────────────────────────────────────────────┘│
		│      9       (((¬q)-->(¬p))-->(p-->r))    -->i 2-8              │
		└─────────────────────────────────────────────────────────────────┘
			10      ((q-->r)-->(((¬q)-->(¬p))-->(p-->r)))    -->i 1-9   
		*/

		var proof_sequent_example_page17 := ProofOfSequent_example_page17();
		print "sequent_example_page17: ";
		PrintSequent(sequent_example_page17);
		print "\nValidity proof for sequent_example_page17: \n";
		PrintSequentProof(sequent_example_page17, proof_sequent_example_page17);
		/*
		sequent_example_page17: (p\/q) |- (q\/p)

		Validity proof for sequent_example_page17:
			1       (p\/q)                     premise                    
		┌─────────────────────────────────────────────────────────────────┐
		│    2       p                          assumption                │
		│    3       (q\/p)                     \/i2 2                    │
		└─────────────────────────────────────────────────────────────────┘
		┌─────────────────────────────────────────────────────────────────┐
		│    4       q                          assumption                │
		│    5       (q\/p)                     \/i1 4                    │
		└─────────────────────────────────────────────────────────────────┘
			6       (q\/p)                     \/e 1,2-3,4-5

		*/

		var proof_sequent_example_page20 := ProofOfSequent_example_page20();
		print "sequent_example_page20: ";
		PrintSequent(sequent_example_page20);
		print "\nValidity proof for sequent_example_page20: \n";
		PrintSequentProof(sequent_example_page20, proof_sequent_example_page20);
		/*
		sequent_example_page20: |- (p-->(q-->p))

		Validity proof for sequent_example_page20: 
		┌─────────────────────────────────────────────────────────────────┐
		│     1       p                         assumption                │
		│┌───────────────────────────────────────────────────────────────┐│
		││    2       q                         assumption               ││
		││    3       p                         copy 1                   ││
		│└───────────────────────────────────────────────────────────────┘│
		│     4       (q-->p)                   -->i 2-3                  │
		└─────────────────────────────────────────────────────────────────┘
			5       (p-->(q-->p))             -->i 1-4
		*/

		var proof_sequent_example_1_20 := ProofOfSequent_example_1_20();
		print "sequent_example_1_20: ";
		PrintSequent(sequent_example_1_20);
		print "\nValidity proof for sequent_example_1_20: \n";
		PrintSequentProof(sequent_example_1_20, proof_sequent_example_1_20);
		/*
		sequent_example_1_20: ((¬p)\/q) |- (p-->q)

		Validity proof for sequent_example_1_20: 
			1       ((¬p)\/q)                 premise
		┌─────────────────────────────────────────────────────────────────┐
		│     2       (¬p)                      assumption                │
		│┌───────────────────────────────────────────────────────────────┐│
		││    3       p                         assumption               ││
		││    4       F                         ¬e 3,2                   ││
		││    5       q                         Fe 4                     ││
		│└───────────────────────────────────────────────────────────────┘│
		│     6       (p-->q)                   -->i 3-5                  │
		└─────────────────────────────────────────────────────────────────┘
		┌─────────────────────────────────────────────────────────────────┐
		│     7       q                         assumption                │
		│┌───────────────────────────────────────────────────────────────┐│
		││    8       p                         assumption               ││
		││    9       q                         copy 7                   ││
		│└───────────────────────────────────────────────────────────────┘│
		│     10      (p-->q)                   -->i 8-9                  │
		└─────────────────────────────────────────────────────────────────┘
			11      (p-->q)                   \/e 1,2-6,7-10
		*/

		var proof_sequent_example_1_21 := ProofOfSequent_example_1_21();
		print "sequent_example_1_21: ";
		PrintSequent(sequent_example_1_21);
		print "\nValidity proof for sequent_example_1_21: \n";
		PrintSequentProof(sequent_example_1_21, proof_sequent_example_1_21);
		/*
		sequent_example_1_21: (p-->q), (p-->(¬q)) |- (¬p)

		Validity proof for sequent_example_1_21:
			1       (p-->q)                    premise
			2       (p-->(¬q))                 premise
		┌─────────────────────────────────────────────────────────────────┐
		│    3       p                          assumption                │
		│    4       q                          -->e 3,1                  │
		│    5       (¬q)                       -->e 3,2                  │
		│    6       F                          ¬e 4,5                    │
		└─────────────────────────────────────────────────────────────────┘
			7       (¬p)                       ¬i 3-6
		*/
	}
}