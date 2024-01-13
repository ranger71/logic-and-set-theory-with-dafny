/* Question/Exercise 1 of 4 */
include "../lectures/lecture04.dfy"

lemma Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(L: bool, R: bool)
	ensures (L <==> R) <==> (L ==> R) && (!L ==> !R)
{
	/*
		This lemma states that logical equivalence (L <==> R) can be proved in two steps:
		(1) that L implies R, and that (2) the negation of L implies the negation of R.
		
		As can be seen here (by the curly braces "{" on line 4 and "}" below this comment), Dafny accepts this claim we no problem.

		Your goal in this exercise is to use the truth tables we've learned for conjunction and negation in lecture01.dfy,
		for logical implication in lecture02.dfy, and for logical equivalence (bi-directional implication) in lecture03.dfy,
		to prove correctness of this claim (such that the final column will have T on each line).
		
		See as an example for this kind of exercise the truth table in lines 13-21 of tutorial03.dfy;
		there, however, the stated property was not correct (as we ended with the truth value T only on 6 of the 8 lines)

		YOUR_SOLUTION_SHOULD_BE_WRITTEN_HERE (inside this comment, to the human reader, not to Dafny):

	L    R    (L <==> R)  (L ==> R)   (!L)    (!R)   (!L ==> !R)  ((L ==> R) && (!L ==> !R))   (L <==> R) <==> (L ==> R) && (!L ==> !R)
   F    F    T           T           T       T      T            T                            T                          
	F    T    F           T           T       F      F            F                            T
	T    F    F           F           F       T      T            F                            T
	T    T    T           T           F       F      T            T                            T
	*/
} 


/* Question/Exercise 2 of 4 */
lemma Q2_DistributivityOfSetUnionOverSetIntersection(A: set, B: set, C: set)
	ensures A+(B*C) == (A+B)*(A+C)
/*
	In this exercise you are expected to write a *full* proof for the lemma;
	as an example, see the proof of "DistributivityOfSetIntersectionOverSetUnion"
	starting on line 167 of lecture04.dfy and continuing on lines 3-44 of tutorial04.dfy;
	note that the proof must be fully justified for the human reader,
	with labels to assertions and the relevant reveal statements where needed,
	as can be seen in the "Distributivity2a" lemma from the tutorial
	(in contrast to the lemma "Distributivity1a" from the lecture, where we did not add labels);
	in case of syntax errors, you solution will NOT be checked.

	YOUR_SOLUTION_SHOULD_BE_WRITTEN_BELOW_THIS_LINE, between curly braces "{" and "}" */
{
	var L, R := A+(B*C), (A+B)*(A+C);
	assert LsubsetR: L <= R by { Distributivity1'(A, B, C, L, R); }
	assert RsubsetL: R <= L by { Distributivity2'(A, B, C, L, R); }
	assert L == R by { reveal LsubsetR, RsubsetL; ExtensionalityUsingSetInclusion(L, R); }
}

lemma Distributivity1'(A: set, B: set, C: set, L: set, R: set)
    requires Pre1: L == A+(B*C)
    requires Pre2: R == (A+B)*(A+C)
    ensures L <= R
{
    forall x | x in L ensures x in R {
        calc {
            x in L;
        == { reveal Pre1; }
            x in A+(B*C);
        ==> { Distributivity1a'(A, B, C, x); }
            x in (A+B)*(A+C);
        == { reveal Pre2; }
            x in R;
        }
    }
}

lemma Distributivity1a'<T>(A: set<T>, B: set<T>, C: set<T>, x: T)
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
lemma Distributivity2'(A: set, B: set, C: set, L: set, R: set)
    requires L == A+(B*C) && R == (A+B)*(A+C)
    ensures R <= L
{}

/* Question/Exercise 3 of 4 */
lemma Q3_SetUnionIsAssociative(A: iset, B: iset, C: iset)
	ensures (A + B) + C == A + (B + C)
/*
	when taking the union of three (possibly-infinite) sets, the order of the operations does not matter;
	this property is known as associativity;
	this is the same in the addition of integers:
	
	assert forall x:int, y: int, z: int :: x+(y+z) == (x+y)+z;

	(whereas for sutraction it does not hold: assert 10-(4-1) == 10-3 == 7 != 5 == 6-1 == (10-4)-1;)
	
	As in exercise 2 above, you are expected to provide a *full* proof, in Dafny, with no errors.

	YOUR_SOLUTION_SHOULD_BE_WRITTEN_BELOW_THIS_LINE, between curly braces "{" and "}" */


/* Question/Exercise 4 of 4 */
lemma preparation_for_Q4_SetDifferenceIs_NOT_Associative()
	ensures !forall A: set<int>, B: set<int>, C: set<int> :: (A - B) - C == A - (B - C)
{
	assert exists A: set<int>, B: set<int>, C: set<int> :: (A - B) - C != A - (B - C) by {
		var A, B, C := Q4_Evidence_That_SetDifferenceIs_NOT_Associative();
		assert (A - B) - C != A - (B - C);
	}
}

lemma Q4_Evidence_That_SetDifferenceIs_NOT_Associative() returns (A: set<int>, B: set<int>, C: set<int>)
	ensures (A - B) - C != A - (B - C)
/*
	Recall from "SquareOfIntegersIsNotMonotonic" in lecture05.dfy how a lemma that returns results
	can be used to disprove a claim by providing evidence for its negation;
	similarly, your goal here is to choose values for A,B,C and demonstrate (using assertions or the "calc" construct)
	how when performing the set difference operation twice, the order of operations DOES matter!

	YOUR_SOLUTION_SHOULD_BE_WRITTEN_BELOW_THIS_LINE, between curly braces "{" and "}" */
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