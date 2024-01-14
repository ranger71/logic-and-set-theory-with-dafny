include "../propositional_logic.dfy"
include "../natural_deduction.dfy"

/*

1.7 Exercises (page 78)

Exercises 1.1

1. Use ¬, ⟶, ∧ and ∨ to express the following declarative sentences in propositional
logic; in each case state what your respective propositional atoms p, q, etc. mean:

(b) Robert was jealous of Yvonne, or he was not in a good mood.

	p: Robert was jealous of Yvonne.
	q: Robert was in a good mood.

	p ∨ ¬q

	(Alternatively, "p ∨ q" if "q" was defined as "Robert was NOT in a good mood.")

(c) If the barometer falls, then either it will rain or it will snow.

	p: The barometer falls
	q: It will rain
	r: It will snow

	p ⟶ q ∨ r

(g) If Smith has installed central heating, then he has sold his car or he has not
    paid his mortgage.

	p: Smith has installed central heating
	q: Smith has sold his car not paid his mortgage
	r: Smith has paid his mortgage

	p ⟶ q ∨ ¬r

	(Or same as the solution to (c) above if "r" was defined as
	"Smith has NOT paid his mortgage".)

2. The formulas of propositional logic below implicitly assume the binding priorities
of the logical connectives put forward in Convention 1.3 [in lecture 1]. Make sure that
you fully understand those conventions by reinserting as many brackets as possible.
For example, given p ∧ q ⟶ r, change it to (p ∧ q) ⟶ r since ∧ binds more tightly
than ⟶.

(d) p ∨ (¬q ⟶ p ∧ r)

Most importantly, the negation and the conjunction bind stronger than the implication:

	p ∨ ((¬q) ⟶ (p ∧ r))

And it's also fine to add further brackets around the entire formula too:

	(p ∨ ((¬q) ⟶ (p ∧ r)))

Section 1.2 Exercise 1(a): let sequent_1_2_1a be ((p/\q)/\r), (s/\t) |- (q/\s)

Validity proof for sequent_1_2_1a: 
    1       ((p/\q)/\r)                 premise
    2       (s/\t)                      premise
    3       (p/\q)                      /\e1 1
    4       q                           /\e2 3      
    5       s                           /\e1 2
    6       (q/\s)                      /\i 4,5

Section 1.2 Exercise 1(b): let sequent_1_2_1b be (p/\q) |- (q/\p)  

Validity proof for sequent_1_2_1b: 
    1       (p/\q)                      premise
    2       q                           /\e2 1
    3       p                           /\e1 1
    4       (q/\p)                      /\i 2,3

Section 1.2 Exercise 1(k): let sequent_1_2_1k be (p-->(q-->r)), (p-->q) |- (p-->r)

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

Section 1.2 Exercise 1(u): let sequent_1_2_1u be (p-->q) |- ((¬q)-->(¬p))

Validity proof for sequent_1_2_1u:
     1       (p-->q)                    premise
┌─────────────────────────────────────────────────────────────────┐
│    2       (¬q)                       assumption                │
│    3       (¬p)                       MT 1,2                    │
└─────────────────────────────────────────────────────────────────┘
     4       ((¬q)-->(¬p))              -->i 2-3

Section 1.2 Exercise 3(a): let sequent_1_2_3a be ((¬p)-->p) |- p

Validity proof for sequent_1_2_3a: 
     1       ((¬p)-->p)                 premise
┌─────────────────────────────────────────────────────────────────┐
│    2       (¬p)                       assumption                │
│    3       p                          -->e 2,1                  │
│    4       F                          ¬e 3,2                    │
└─────────────────────────────────────────────────────────────────┘
     5       p                          PBC 2-4

Section 1.2 Exercise 3(c): let sequent_1_2_3c be (p\/q), (¬q) |- p

Validity proof for sequent_1_2_3c: 
     1       (p\/q)                     premise                    
     2       (¬q)                       premise
┌─────────────────────────────────────────────────────────────────┐
│    3       p                          assumption                │
│    4       p                          copy 3                    │
└─────────────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────────────┐
│    5       q                          assumption                │
│    6       F                          ¬e 5,2                    │
│    7       p                          Fe 6                      │
└─────────────────────────────────────────────────────────────────┘
     8       p                          \/e 1,3-4,5-7

Section 1.2 optional Exercise 3(m): let sequent_1_2_3m be ((p/\q)-->r) |- ((p-->r)\/(q-->r))

Validity proof for sequent_1_2_3m:
        1       ((p/\q)-->r)            premise
        2       (r\/(¬r))               LEM
┌─────────────────────────────────────────────────────────────────┐
│       3       r                       assumption                │
│┌───────────────────────────────────────────────────────────────┐│
││      4       p                       assumption               ││
││      5       r                       copy 3                   ││
│└───────────────────────────────────────────────────────────────┘│
│       6       (p-->r)                 -->i 4-5                  │
│       7       ((p-->r)\/(q-->r))      \/i1 6                    │
└─────────────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────────────┐
│       8       (¬r)                    assumption                │
│       9       (p\/(¬p))               LEM                       │
│┌───────────────────────────────────────────────────────────────┐│
││      10      p                       assumption               ││
││      11      (q\/(¬q))               LEM                      ││
││┌─────────────────────────────────────────────────────────────┐││
│││     12      q                       assumption              │││
│││     13      (p/\q)                  /\i 10,12               │││
│││     14      r                       -->e 13,1               │││
│││     15      F                       ¬e 14,8                 │││
│││     16      ((p-->r)\/(q-->r))      Fe 15                   │││
││└─────────────────────────────────────────────────────────────┘││
││┌─────────────────────────────────────────────────────────────┐││
│││     17      (¬q)                    assumption              │││
│││┌───────────────────────────────────────────────────────────┐│││
││││    18      q                       assumption             ││││
││││    19      F                       ¬e 18,17               ││││
││││    20      r                       Fe 19                  ││││
│││└───────────────────────────────────────────────────────────┘│││
│││     21      (q-->r)                 -->i 18-20              │││
│││     22      ((p-->r)\/(q-->r))      \/i2 21                 │││
││└─────────────────────────────────────────────────────────────┘││
││      23      ((p-->r)\/(q-->r))      \/e 11,12-16,17-22       ││
│└───────────────────────────────────────────────────────────────┘│
│┌───────────────────────────────────────────────────────────────┐│
││      24      (¬p)                    assumption               ││
││┌─────────────────────────────────────────────────────────────┐││
│││     25      p                       assumption              │││
│││     26      F                       ¬e 25,24                │││
│││     27      r                       Fe 26                   │││
││└─────────────────────────────────────────────────────────────┘││
││      28      (p-->r)                 -->i 25-27               ││
││      29      ((p-->r)\/(q-->r))      \/i1 28                  ││
│└───────────────────────────────────────────────────────────────┘│
│       30      ((p-->r)\/(q-->r))      \/e 9,10-23,24-29         │
└─────────────────────────────────────────────────────────────────┘
        31      ((p-->r)\/(q-->r))      \/e 2,3-7,8-30             

An alternative solution to 3(m): again, let sequent_1_2_3m be ((p/\q)-->r) |- ((p-->r)\/(q-->r))

What follows is a much shorter proof, by contradiction instead of case analysis, submitted by two of our students:
       1       ((p/\q)-->r)             premise
┌─────────────────────────────────────────────────────────────────┐
│      2       (¬((p-->r)\/(q-->r)))    assumption                │
│┌───────────────────────────────────────────────────────────────┐│
││     3       p                        assumption               ││
││┌─────────────────────────────────────────────────────────────┐││
│││    4       q                        assumption              │││
│││    5       (p/\q)                   /\i 3,4                 │││
│││    6       r                        -->e 5,1                │││
││└─────────────────────────────────────────────────────────────┘││
││     7       (q-->r)                  -->i 4-6                 ││
││     8       ((p-->r)\/(q-->r))       \/i2 7                   ││
││     9       F                        ¬e 8,2                   ││
││     10      r                        Fe 9                     ││
│└───────────────────────────────────────────────────────────────┘│
│      11      (p-->r)                  -->i 3-10                 │
│      12      ((p-->r)\/(q-->r))       \/i1 11                   │
│      13      F                        ¬e 12,2                   │
└─────────────────────────────────────────────────────────────────┘
       14      ((p-->r)\/(q-->r))       PBC 2-13
*/

module Logic_Assignment_1_Solution {
	import opened PropositionalLogic
	import opened NaturalDeduction

	// Exercises 1.2

	// 1. Prove the validity of the following sequents:

	// (a)   (p ∧ q) ∧ r, s ∧ t ⊢ q ∧ s
	const sequent_1_2_1a := ([AND(AND(p, q), r), AND(s, t)], AND(q, s))

	method ProofOfSequent_1_2_1a() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_1a, proof)
	{
		var Step1 := (AND(AND(p, q), r), Premise);
		assert CorrectProofStep(Step1, sequent_1_2_1a.0, []);
		var Step2 := (AND(s, t), Premise);
		assert CorrectProofStep(Step2, sequent_1_2_1a.0, []);
		var Step3 := (AND(p, q), AND_Elimination_1(Step1));
		//assert CorrectProofStep(Step3, sequent_1_2_1a.0, []);
		var Step4 := (q, AND_Elimination_2(Step3));
		var Step5 := (s, AND_Elimination_1(Step2));
		//assert CorrectProofStep(Step4, sequent_1_2_1a.0, []);
		//assert CorrectProofStep(Step5, sequent_1_2_1a.0, []);
		var Step6 := (AND(q, s), AND_Introduction(Step4, Step5));
		assert CorrectProofStep(Step6, sequent_1_2_1a.0, []);
		proof := Step6;
	}

	// (b)   p ∧ q ⊢ q ∧ p
	const sequent_1_2_1b := ([AND(p, q)], AND(q, p))

	method ProofOfSequent_1_2_1b() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_1b, proof)
	{
		var Step1 := (AND(p, q), Premise);
		var Step2 := (q, AND_Elimination_2(Step1));
		var Step3 := (p, AND_Elimination_1(Step1));
		var Step4 := (AND(q, p), AND_Introduction(Step2, Step3));
		proof := Step4;
	}

	// (k)   p ⟶ (q ⟶ r), p ⟶ q ⊢ p ⟶ r
	const sequent_1_2_1k := ([IMPLIES(p, IMPLIES(q, r)), IMPLIES(p, q)], IMPLIES(p, r))

	method ProofOfSequent_1_2_1k() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_1k, proof)
	{
		var Step1 := (IMPLIES(p, IMPLIES(q, r)), Premise);
		var Step2 := (IMPLIES(p, q), Premise);
		var Step3 := (p, Assumption);
		// interestingly, steps 4 and 5 are printed in the reverse order;
		// this is because our printing method traverses the proof as a tree
		// in a depth-first left-to-ritht order, and issues step numbers accordingly
		// (with one exception that assumptions are always numbered/printed first);
		// as "q" (from our Step5 below) is the first argument to the IMPLIES_Elimination
		// justification of Step 5, it is given an earlier number than the "IMPLIES(q, r)";
		// note that both numberings are consistent and therefore correct
		var Step4 := (IMPLIES(q, r), IMPLIES_Elimination(Step3, Step1));
		var Step5 := (q, IMPLIES_Elimination(Step3, Step2));
		var Step6 := (r, IMPLIES_Elimination(Step5, Step4));
		var Box_3_6 := (Step3.0, Step6);
		var Step7 := (IMPLIES(p, r), IMPLIES_Introduction(Box_3_6));
		proof := Step7;
	}

	// (u)   p ⟶ q ⊢ ¬q ⟶ ¬p
	const sequent_1_2_1u := ([IMPLIES(p, q)], IMPLIES(NOT(q), NOT(p)))

	method ProofOfSequent_1_2_1u() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_1u, proof)
	{
		var Step1 := (IMPLIES(p, q), Premise);
		var Step2 := (NOT(q), Assumption);
		var Step3 := (NOT(p), MT(Step1, Step2));
		var Box_2_3 := (Step2.0, Step3);
		var Step4 := (IMPLIES(NOT(q), NOT(p)), IMPLIES_Introduction(Box_2_3));
		proof := Step4;
	}

	// 3. Prove the validity of the sequents below:

	// (a)   ¬p ⟶ p ⊢ p
	const sequent_1_2_3a := ([IMPLIES(NOT(p), p)], p)

	method ProofOfSequent_1_2_3a() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_3a, proof)
	{
		var Step1 := (IMPLIES(NOT(p), p), Premise);
		var Step2 := (NOT(p), Assumption);
		var Step3 := (p, IMPLIES_Elimination(Step2, Step1));
		var Step4 := (FALSE, NOT_Elimination(Step3, Step2));
		var Box_2_4 := (Step2.0, Step4);
		var Step5 := (p, PBC(Box_2_4));
		proof := Step5;
	}

	// (c)   p ∨ q, ¬q ⊢ p
	const sequent_1_2_3c := ([OR(p, q), NOT(q)], p)

	method ProofOfSequent_1_2_3c() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_3c, proof)
	{
		var Step1 := (OR(p, q), Premise);
		var Step2 := (NOT(q), Premise);
		var Step3 := (p, Assumption);
		var Step4 := (p, Copy(Step3));
		var Box_3_4 := (Step3.0, Step4);
		var Step5 := (q, Assumption);
		var Step6 := (FALSE, NOT_Elimination(Step5, Step2));
		var Step7 := (p, Bottom_Elimination(Step6));
		var Box_5_7 := (Step5.0, Step7);
		var Step8 := (p, OR_Elimination(Step1, Box_3_4, Box_5_7));
		proof := Step8;
	}

	// (m)   p ∧ q ⟶ r ⊢ (p ⟶ r) ∨ (q ⟶ r)
	const sequent_1_2_3m := ([IMPLIES(AND(p, q), r)], OR(IMPLIES(p, r), IMPLIES(q, r)))

   // [see below two solutions: one presented in class, the other (much much shorter solution!) proposed by two students]
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
		proof := Step31;
	}

	method ProofOfSequent_1_2_3m'() returns (proof: SequentProof)
		ensures CorrectSequentProof(sequent_1_2_3m, proof)
	{
		var Step1 := (IMPLIES(AND(p, q), r), Premise);
		var Step2 := (NOT(OR(IMPLIES(p, r), IMPLIES(q, r))), Assumption);
		var Step3 := (p, Assumption);
		var Step4 := (q, Assumption);
		var Step5 := (AND(p, q), AND_Introduction(Step3, Step4));
		var Step6 := (r, IMPLIES_Elimination(Step5, Step1));
		var Box_4_6 := (Step4.0, Step6);
		var Step7 := (IMPLIES(q, r), IMPLIES_Introduction(Box_4_6));
		var Step8 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Introduction_2(Step7));
		var Step9 := (FALSE, NOT_Elimination(Step8, Step2));
		var Step10 := (r, Bottom_Elimination(Step9));
		var Box_3_10 := (Step3.0, Step10);
		var Step11 := (IMPLIES(p, r), IMPLIES_Introduction(Box_3_10));
		var Step12 := (OR(IMPLIES(p, r), IMPLIES(q, r)), OR_Introduction_1(Step11));
		var Step13 := (FALSE, NOT_Elimination(Step12, Step2));
		var Box_2_13 := (Step2.0, Step13);
		var Step14 := (OR(IMPLIES(p, r), IMPLIES(q, r)), PBC(Box_2_13));
		proof := Step14;
	}

	method Main() {
		var proof_sequent_1_2_1a := ProofOfSequent_1_2_1a();
		print "Section 1.2 Exercise 1(a): let sequent_1_2_1a be ";
		PrintSequent(sequent_1_2_1a);
		print "\nValidity proof for sequent_1_2_1a: \n";
		PrintSequentProof(sequent_1_2_1a, proof_sequent_1_2_1a);

		var proof_sequent_1_2_1b := ProofOfSequent_1_2_1b();
		print "Section 1.2 Exercise 1(b): let sequent_1_2_1b be ";
		PrintSequent(sequent_1_2_1b);
		print "\nValidity proof for sequent_1_2_1b: \n";
		PrintSequentProof(sequent_1_2_1b, proof_sequent_1_2_1b);

		var proof_sequent_1_2_1k := ProofOfSequent_1_2_1k();
		print "Section 1.2 Exercise 1(k): let sequent_1_2_1k be ";
		PrintSequent(sequent_1_2_1k);
		print "\nValidity proof for sequent_1_2_1k: \n";
		PrintSequentProof(sequent_1_2_1k, proof_sequent_1_2_1k);

		var proof_sequent_1_2_1u := ProofOfSequent_1_2_1u();
		print "Section 1.2 Exercise 1(u): let sequent_1_2_1u be ";
		PrintSequent(sequent_1_2_1u);
		print "\nValidity proof for sequent_1_2_1u: \n";
		PrintSequentProof(sequent_1_2_1u, proof_sequent_1_2_1u);

		var proof_sequent_1_2_3a := ProofOfSequent_1_2_3a();
		print "Section 1.2 Exercise 3(a): let sequent_1_2_3a be ";
		PrintSequent(sequent_1_2_3a);
		print "\nValidity proof for sequent_1_2_3a: \n";
		PrintSequentProof(sequent_1_2_3a, proof_sequent_1_2_3a);

		var proof_sequent_1_2_3c := ProofOfSequent_1_2_3c();
		print "Section 1.2 Exercise 3(c): let sequent_1_2_3c be ";
		PrintSequent(sequent_1_2_3c);
		print "\nValidity proof for sequent_1_2_3c: \n";
		PrintSequentProof(sequent_1_2_3c, proof_sequent_1_2_3c);

		var proof_sequent_1_2_3m := ProofOfSequent_1_2_3m();
		print "Section 1.2 optional Exercise 3(m): let sequent_1_2_3m be ";
		PrintSequent(sequent_1_2_3m);
		print "\nValidity proof for sequent_1_2_3m: \n";
		PrintSequentProof(sequent_1_2_3m, proof_sequent_1_2_3m);

		var proof_sequent_1_2_3m' := ProofOfSequent_1_2_3m'();
		print "An alternative solution to 3(m): again, let sequent_1_2_3m be ";
		PrintSequent(sequent_1_2_3m);
		print "\nWhat follows is a much shorter proof, by contradiction instead of case analysis, submitted by two of our students: \n";
		PrintSequentProof(sequent_1_2_3m, proof_sequent_1_2_3m');
	}
}