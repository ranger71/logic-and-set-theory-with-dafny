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
	}
}