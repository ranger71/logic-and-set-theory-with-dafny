include "set_theory/assignments/definitions_until_lecture09.dfy"
include "logic/propositional_logic.dfy"
include "logic/truth_tables.dfy"
include "logic/natural_deduction.dfy"

/*

Dafny 2024 talk on the LST course

[sources: Uri Abraham's course @ BGU, Huth and Ryan's textbook, Leino's "Dafny Power User: Different Styles of Proofs"]

1) Dafny as a proof assistant: set theory
2) Dafny as a (verification-aware) programming language: propositional logic
3) Dafny as a teaching assistant! [providing instant feedback for students; help in the grading process (*)]

(*) on relations-related quizzes, on natural-deduction proofs [see 31 vs 14-step proof story below]

// selected proofs - from past and present course assignments:
*/

module Dafny24_Talk_SetTheory {
	import opened SetTheory_Definitions

	// 1) set theory

	// a) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/set_theory/assignments/assignment1%20-%20partial%20solution.dfy#L32

	// - lemmas
	// - assert ... by
	// - labels / reveal
	// - forall ... ensures
	// - calc

	// Question/Exercise 2 of 4
	lemma Q2_DistributivityOfSetUnionOverSetIntersection(A: set, B: set, C: set)
		ensures A+(B*C) == (A+B)*(A+C)
	{
		var L, R := A+(B*C), (A+B)*(A+C);
		assert LsubsetR: L <= R by { Distributivity1(A, B, C, L, R); }
		assert RsubsetL: R <= L by { Distributivity2(A, B, C, L, R); }
		assert L == R by { reveal LsubsetR, RsubsetL; ExtensionalityUsingSetInclusion(L, R); }
	}

	lemma Distributivity1(A: set, B: set, C: set, L: set, R: set)
		requires Pre1: L == A+(B*C)
		requires Pre2: R == (A+B)*(A+C)
		ensures L <= R
	{
		forall x | x in L ensures x in R {
			calc {
				x in L;
			== { reveal Pre1; }
				x in A+(B*C);
			==> { Distributivity1a(A, B, C, x); }
				x in (A+B)*(A+C);
			== { reveal Pre2; }
				x in R;
			}
		}
	}

	lemma Distributivity1a<T>(A: set<T>, B: set<T>, C: set<T>, x: T)
		requires Pre: x in A+(B*C)
		ensures x in (A+B)*(A+C)
	{
		if x in A {
			assert 1: x in A+B; // by definition of set union
			assert 2: x in A+C; // by definition of set union
			assert x in (A+B)*(A+C) by { reveal 1,2; }
		}
		else
		{
			assert 3: x !in A; // negation of the guard
			assert 4: x in B*C by { reveal Pre,3; } // and by definition of set union
			assert 5: x in B by { reveal 4; } // and the definition of intersection
			assert 6: x in C by { reveal 4; } // and again by the definition of intersection
			assert 7: x in A+B by { reveal 5; } // and by definition of set union
			assert 8: x in A+C by { reveal 6; } // and by definition of set union
			assert x in (A+B)*(A+C) by { reveal 7,8; }
		}
	}

	// this could be proved in a similar way to Distributivity1
	lemma Distributivity2(A: set, B: set, C: set, L: set, R: set)
		requires L == A+(B*C) && R == (A+B)*(A+C)
		ensures R <= L
	{}

	// b) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/set_theory/assignments/assignment1%20-%20partial%20solution.dfy#L124

	// - existential witness returned from a lemma
	// - calc on booleans + calc on sets
	// - Dafny assists by *rejecting* incorrect answers

	lemma Q4_Evidence_That_SetDifferenceIs_NOT_Associative() returns (A: set<int>, B: set<int>, C: set<int>)
		ensures (A - B) - C != A - (B - C)
	{
		var EMPTY: set<int>, ONE_AND_TWO := {}, {1,2};
		A, B, C := {1,2,3}, {1,2,3}, {1,2};
		calc {
			(A - B) - C != A - (B - C);
		== { assert A - (B - C) == {1,2}; }
			EMPTY != {1,2};
		==
			true;
		}
		// one more way to prove correctness:
		calc {
			(A - B) - C;
		==
			EMPTY;
		!=
			ONE_AND_TWO;
		==
			A - (B - C);
		}
	}

	// c) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/set_theory/assignments/assignment2%20-%20with%20solution%20of%20Q1-Q6.dfy#L155

	// - binary relation as a type
	// - set equality as bi-directional set inclusion

	lemma Q6_InverseDomain<T(!new)>(R: BinaryRelation<T,T>, InverseR: BinaryRelation<T,T>, A: iset<T>)
		requires pre1: RelationOn(R, A)
		requires pre2: InverseR == InverseRelation(R)
		ensures Range(R) == Domain(InverseR)
	{
		// <=
		forall b | b in Range(R) ensures b in Domain(InverseR) {
			assert 3: b in Range(R);
			assert b in Domain(InverseR) by {reveal pre1,pre2,3;}
		}
		// >=
		forall b | b in Domain(InverseR) ensures b in Range(R) {
			assert 4: b in Domain(InverseR);
			assert b in Range(R) by {reveal pre1,pre2,4;}
		}
	}

	// d) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/set_theory/assignments/assignment3%20-%20with%20solution.dfy#L110

	// - proving cardinal equivalence (A4 ~ B4)
	// - interesting to see here:
	//   - how little changes are rejected by Dafny
	//   - how Dafny proves injective by itself but NOT surjective
	ghost const A4 := iset x: int | x > 5
	ghost const B4 := iset x: int | x < 5

	ghost const F4a := iset x, y | x in A4 && y in B4 && x == 10-y :: (x,y)
	ghost const F4b := iset x, y | x in A4 && y in B4 && x == 9-y :: (x,y)

	// complete the following definition (choosing F4a or F4b)
	ghost function goodF4(): BinaryRelation<int, int> {
		F4a // solution
	}

	// complete the following definition too (choosing again F4a or F4b)
	ghost function badF4(): BinaryRelation<int, int> {
		F4b // solution
	}

	// goal: prove...
	lemma LemmaGoodF4() returns (F: BinaryRelation<int, int>)
		ensures F == goodF4()
		ensures ValidFunctionDomain(F, A4) && Range(F) <= B4 && BijectiveFunction(F, A4, B4)
	{ // a possible solution
		F := goodF4();
		assert ValidFunctionDomain(F, A4) by {
			forall x | x in A4 ensures x in Domain(F) {
				assert x > 5;
				var y := 10-x;
				assert y < 5;
				assert y in B4;
				assert (x,y) in F;
			}
		}
		assert Range(F) <= B4;
		assert BijectiveFunction(F, A4, B4) by {
			assert InjectiveFunction(F);
			assert SurjectiveFunction(F, A4, B4) by {
				forall y | y in B4 ensures exists x :: x in A4 && (x,y) in F {
					assert y < 5;
					var x' := 10-y;
					assert x' > 5;
					assert x' in A4;
				}
			}
		}
	}

	// goal: prove...
	lemma LemmaBadF4(F: BinaryRelation<int, int>)
		requires F == badF4()
		ensures ValidFunction(F) && A4 == Domain(F) && Range(F) <= B4
		ensures !SurjectiveFunction(F, A4, B4)
	{ // a possible solution
		assert ValidFunction(F);
		assert A4 == Domain(F) by {
			assert A4 <= Domain(F) by {
				forall x | x in A4 ensures x in Domain(F) {
					assert x > 5;
					var y := 9-x;
					assert y < 4;
					assert y in B4;
					assert (x,y) in F;
				}
			}
			assert A4 >= Domain(F);
		}
		assert Range(F) <= B4;
		assert !SurjectiveFunction(F, A4, B4) by {
			var y := 4;
			assert 9-y == 5 && 5 !in A4;
			assert y !in Range(F);
			assert !SurjectiveFunction'(F, A4, B4);
			EquivalentSurjectiveDefinitions(F, A4, B4);
		}
	}

	// e) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/set_theory/assignments/A_2022_solution.dfy#L28

	// a quizz exercise about equivalence relations
	// Dafny assists here in verifying correctness of unexpected solutions

	ghost function f2a(): BinaryRelation<int, int>
	{
		iset{(4,7), (5,4), (5,5), (5,6), (6,6), (6,8), (7,5), (8,6), (8,4)}
	}

	// exercise: define the following two functions such that all assertions in the method below will hold 
	ghost function f2b(): BinaryRelation<int, int> {
		iset{(4,7), (5,4), (6,8), (8,6), (8,4)}
	}

	ghost function f2c(): BinaryRelation<int, int> {
		iset{(7,6), (7,7), (5,7)} // interestingly, adding either (6,5) or (5,7) is fine too (but not both)
	}

	ghost const A2: iset<int> := iset{5,6,7}
	ghost const R2: BinaryRelation<int, int> := (f2a() - f2b()) + f2c()

	method Q2()
	{
		assert f2a() !! f2c();
		assert f2b() < f2a();
		assert forall x,y :: (x,y) in f2b() ==> x !in A2 || y !in A2;
		assert RelationOn(R2, A2);
		assert Reflexive(R2, A2);
		assert Transitive(R2);
		assert !EquivalenceRelation(R2, A2) by {
			assert !Symmetric(R2);
		}
	}
}

module Dafny24_Talk_Logic {
	import opened PropositionalLogic
	import opened TruthTables
	import opened NaturalDeduction

	// 2) propositional logic [source: Huth and Ryan's textbook]:

	// natural deduction

	// a) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/logic/assignments/logic-assignment-1-solution.dfy#L76

	/*
		Validity proof for sequent_1_2_1k: 
		1       (p-->(q-->r))              premise
		2       (p-->q)                    premise
	┌─────────────────────────────────────────────────────────────────┐
	│    3       p                          assumption                │
	│    4       q                          -->e 3,2                  │
	│    5       (q-->r)                    -->e 3,1                  │
	│    6       r                          -->e 4,5                  │
	└─────────────────────────────────────────────────────────────────┘
		7       (p-->r)                    -->i 3-6
	*/
	// (k)   p ⟶ (q ⟶ r), p ⟶ q ⊢ p ⟶ r
	const sequent_1_2_1k := ([IMPLIES(p, IMPLIES(q, r)), IMPLIES(p, q)], IMPLIES(p, r))

	method ProofOfSequent_1_2_1k() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_1k, proof)
	{
		var Step1 := (IMPLIES(p, IMPLIES(q, r)), Premise);
		var Step2 := (IMPLIES(p, q), Premise);
		var Step3 := (p, Assumption);
		var Step4 := (IMPLIES(q, r), IMPLIES_Elimination(Step3, Step1));
		var Step5 := (q, IMPLIES_Elimination(Step3, Step2));
		var Step6 := (r, IMPLIES_Elimination(Step5, Step4));
		var Box_3_6 := (Step3.0, Step6);
		var Step7 := (IMPLIES(p, r), IMPLIES_Introduction(Box_3_6));
		proof := Step7;
	}

	// b) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/logic/assignments/logic-assignment-1-solution.dfy#L480

	// - a long (31-step) proof (mostly by case analysis)
	
	// c) https://github.com/ranger71/logic-and-set-theory-with-dafny/blob/main/logic/assignments/logic-assignment-1-solution.dfy#L486

	// - a much shorter (14-step) proof-by-contradiction submitted by students to the same exercise above
	// - thanks Dafny for assisting in verifying correctness
	//   - this assignment was prepared "on paper"
	//   - in grading we were able to formulate and verify correctness using Dafny
	
	// d) proof debugging:

	// an incorrect attempt at a proof submitted by students, with a small mistake;
	// when we fix it, Dafny confirms correctness!

	/* Exercise 16 (a) from Section 1.4

	sequent_16_a: (A/\(¬B)) |- (¬(A-->B))

	     1       (A/\(¬B))                  premise
	┌─────────────────────────────────────────────────────────────────┐
	│    2       (A-->B)                    assumption                │
	│    3       A                          /\e1 1                    │
	│    4       (¬B)                       /\e2 1                    │
	│    5       (¬A)                       MT 2,4                    │
	│    6       F                          ¬e 3,5                    │
	└─────────────────────────────────────────────────────────────────┘
		7       (¬(A-->B))                 ¬i 2-6
	*/

	const sequent_16_a := ([AND(A, NOT(B))], NOT(IMPLIES(A, B)))

	method CorrectSequenta()
		ensures CorrectSequent(sequent_16_a)
	{
		var proof_sequent_16_a := ProofOfSequent_16_a();
		assert exists proof: SequentProof :: CorrectSequentProof(sequent_16_a, proof) by {
			assert CorrectSequentProof(sequent_16_a, proof_sequent_16_a);
		}
	}

	method ProofOfSequent_16_a() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_16_a, proof)
	{
		var Step1, Step2, Step3, Step4,Step5,Step6,Step7;
		var Box_1;
	
		Step1 := (IMPLIES(A,B), Assumption);
		Step2 := (AND(A,NOT(B)), Premise);
		Step3 := (NOT(B), AND_Elimination_2(Step2));
		Step4 := (NOT(A), MT(Step1,Step3));
		Step5 := (A, AND_Elimination_1(Step2));
///		Step6 := (FALSE,NOT_Elimination(Step4,Step5)); /// a small mistake
		Step6 := (FALSE,NOT_Elimination(Step5,Step4)); /// a fix (thanks Dafny!)
		Box_1 := (Step1.0,Step6);
		Step7 := (NOT(IMPLIES(A,B)),NOT_Introduction(Box_1));
		proof := Step7;
	}


	// e) truth tables

	/*
		p  q  r ¬p  ¬r  ¬p∧q   q∨¬r   p∧(q∨¬r)   ¬p∧q⟶p∧(q∨¬r)
		--------------------------------------------------------
		T  T  T  F  F     F     T        T             T
		T  T  F  F  T     F     T        T             T
		T  F  T  F  F     F     F        F             T
		T  F  F  F  T     F     T        T             T
		F  T  T  T  F     T     T        F             F
		F  T  F  T  T     T     T        F             F
		F  F  T  T  F     F     F        F             T
		F  F  F  T  T     F     T        F             T

		The ultimate column in the truth table of the formula (((¬p)/\q)-->(p/\(q\/(¬r)))) is

		map[
			map[['p'] := false, ['q'] := false, ['r'] := false] := true, 
			map[['p'] := false, ['q'] := false, ['r'] := true] := true, 
			map[['p'] := false, ['q'] := true, ['r'] := false] := false, 
			map[['p'] := true, ['q'] := false, ['r'] := false] := true, 
			map[['p'] := false, ['q'] := true, ['r'] := true] := false, 
			map[['p'] := true, ['q'] := false, ['r'] := true] := true, 
			map[['p'] := true, ['q'] := true, ['r'] := false] := true, 
			map[['p'] := true, ['q'] := true, ['r'] := true] := true]
	*/
	const f2b := IMPLIES(AND(NOT(p),q),AND(p,OR(q,NOT(r))))

	method Main() {
 		var proof_sequent_1_2_1k := ProofOfSequent_1_2_1k();
		print "Section 1.2 Exercise 1(k): let sequent_1_2_1k be ";
		PrintSequent(sequent_1_2_1k);
		print "\nValidity proof for sequent_1_2_1k: \n";
		PrintSequentProof(sequent_1_2_1k, proof_sequent_1_2_1k);

		print "16(a)\n";
		var proof_sequent_a := ProofOfSequent_16_a();
		print "sequent_example_a: ";
		PrintSequent(sequent_16_a);
		print "\nValidity proof for sequent_16_a: \n";
		PrintSequentProof(sequent_16_a, proof_sequent_a);

		print "2(b)\n";
		print "The ultimate column in the truth table of the formula ", FormulaToString(f2b), " is ",
				TruthTableColumn(f2b, Variables(f2b)), "\n";
	}
}