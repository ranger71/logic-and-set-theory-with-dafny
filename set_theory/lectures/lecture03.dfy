/*

lecture 3: first proofs (of lemmas)

- predicates
- using Dafny's "forall ... ensures" construct
- giving labels to assertions and "requires" clauses, and referring to them with "reveal"
  (to justify correctness of the next assertion)
- transitivity of the set inclusion relation
- some further properties of sets and their operations
- a first look on the negation of a quantifier

*/

include "lecture02.dfy"

module Lecture03 {
	import opened Lecture01
	import opened Lecture02
	// but first, one more truth table: logical equivalence (bidirectional implication)
	/*

	The truth table of equivalence (<-->, in Dafny <==>):

	P  Q  (P <--> Q)
	F  F  T
	F  T  F
	T  F  F
	T  T  T

	*/

	//function IsSubset(A: set, B: set): bool
	predicate IsSubset(A: set, B: set) // <=
	{
		forall n :: n in A ==> n in B // same as the next line
		//forall n :: if n in A then n in B else true // same as "A <= B"
	}

	lemma IntersectionIsSubsetOfBoth'(A: set, B: set, C: set)
		requires pre: C == SetIntersection(A, B) // == A*B
		ensures IsSubset(C, A) // Post1: C <= A
		ensures IsSubset(C, B) // Post2: C <= B
	{
		//reveal pre; // we prefer not to reveal the precondition too early, but rather only where needed,
		// in order to demonstrate our understanding

		// Post1:
		assert IsSubset(C, A) by {
			assert forall n :: n in C ==> n in A by {
				//assert n in C; // the variable "n" is not defined here (it is out of scope)
				forall m | m in C ensures m in A {
					assert L1: m in C; //  we know this from the "|" of the forall statement above (the "such that" condition)
					//assert m in A;// by { reveal pre; } //  this is what we need to show/demonstrate/prove
					assert L2: m in A && m in B by { reveal pre,L1; } // and by the definition of SetIntersection
					assert m in A by { reveal L2; AndImpliesBoth(m in A, m in B); } //  this is what we need to show/demonstrate/prove
				}
			}
		}
		// Post2 can be proved in a similar way
		assert IsSubset(C, B) by { reveal pre; }
	}

	// this is obviously true, still we formulate it as another example for a lemma and the way it can be used
	// exercise: prove this using a truth table
	lemma AndImpliesBoth(P: bool, Q: bool)
		ensures (P && Q) ==> P
		ensures (P && Q) ==> Q
	{}

	ghost predicate IsTrue(P: PropositionalFormula) {
		ValidFormula(P) && forall assignment: map<nat, bool> :: Identifiers(P) <= assignment.Keys ==> Value(P, assignment) == true
	}
/*
	ghost predicate IsTrue(P: PropositionalFormula) {
		ValidFormula(P) &&
		var VarIds := Identifiers(P);
		var Column := TruthTableColumn(P, VarIds);
		assert Column.Keys == AllRows(VarIds); // ???
		forall Row :: Row in AllRows(VarIds) ==> Column[Row] == true // how do we make sure Row is indeed in Column.Keys?
	}
*/
	lemma AndImpliesBoth'(P: PropositionalFormula, Q: PropositionalFormula)
		requires ValidFormula(P) && ValidFormula(Q)
		ensures IsTrue(IMPLIES(AND(P, Q), P))
		ensures IsTrue(IMPLIES(AND(P, Q), Q))

	predicate IsProperSubset(A: set, B: set)
	{
		IsSubset(A, B) && (exists m :: m in B && m !in A)
	}

	// could be written also this way:
	predicate IsProperSubset2(A: set, B: set)
	{
		IsSubset(A, B) &&
		SetDifference(B, A) != {} 
	}

	// could also be written also this way:
	predicate IsProperSubset3(A: set, B: set)
	{
		IsSubset(A, B) &&
		|SetDifference(B, A)| != 0 
	}

	// and could also be written this way:
	predicate IsProperSubset4(A: set, B: set)
	{
		IsSubset(A, B) &&
		|A| < |B|
	}

	// or this way:
	predicate IsProperSubset5(A: set, B: set)
	{
		IsSubset(A, B) &&
		A != B // how to prove equality (or inequality) of two sets we will learn next week
	}

	// exercise: try to prove, or find a problem in the definition
	lemma {:verify false} EquivalentDefinitionsOfProperSubset(A: set, B: set)
		ensures IsProperSubset(A, B) == IsProperSubset2(A, B) == IsProperSubset3(A, B) == IsProperSubset4(A, B) == IsProperSubset5(A, B)
	{}

	lemma {:verify true} TransitivityOfSetInclusion(A: set, B: set, C: set)
		requires pre1: IsSubset(A, B)
		requires pre2: IsSubset(B, C)
		ensures IsSubset(A, C)
	{
		assert forall n :: n in A ==> n in C by { // in the future we will not write this assertion
			forall m | m in A ensures m in C {
				assert MemberOfA: m in A; //  we know this from the "|" of the forall statement above (the "such that" condition)
				//assert m in C; //  this is what we need to show/demonstrate/prove
				assert MemberOfB: m in B by { reveal MemberOfA,pre1; } // and by the definition of IsSubset
				assert MemberOfC: m in C by { reveal MemberOfB,pre2; } // and again by the definition of IsSubset
				reveal MemberOfC; // could skip this reveal by not providing a label to the assertion above
			}
		}
	}

	// whenever the intersection is empty we say the sets are disjoint (זרות)
	predicate DisjointSets(A: set, B: set) { SetIntersection(A, B) == {} }

	method M3a() {
		assert {1,3,5} + {2,4,6} == {1,2,3,4,5,6};
		assert {1,3,5} * {2,4,6} == {};
		assert DisjointSets({1,3,5}, {2,4,6});
		assert SetIntersection({1,3,4,5}, {2,4,6}) == {4}; // a set with one element is known as a singleton ("יחידון")
		assert !DisjointSets({1,3,4,5}, {2,4,6}) by { assert 4 in {1,3,4,5} && 4 in {2,4,6}; } // the intersection is not empty: it is the singleton {4}
	}

	lemma SubsetsInDafny(A: set, B: set)
		ensures A<=B <==> IsSubset(A, B)
		ensures A>=B <==> IsSubset(B, A) // we can also say that A is a superset of B
	{}

	// two general properties: each set has the empty set and the set itself as subsets
	lemma EmptySubset(A: set)
		ensures IsSubset({}, A)
	{}

	lemma SelfSubset(A: set)
		ensures IsSubset(A, A)
	{}

	lemma NotSelfProperSubset(A: set)
		ensures !IsProperSubset(A, A)
	{}

	ghost predicate IsSuperset(A: iset, B: iset)
	{
		forall n :: n in B ==> n in A // same as "A >= B"
	}

	// the union is always a superset of both sets
	lemma UnionIsSuperset(A: iset, B: iset)
		ensures IsSuperset(SetUnion(A, B), A)
		ensures IsSuperset(SetUnion(A, B), B)
	{} // Exercise: prove this by choosing an element and following the definition (of set-union this time)

	// example of negation of forall:
	lemma {:verify false} DeMorganOfForall(A: set<int>)
		ensures !(forall x :: x in A <==> x%2 == 0) <==> (exists x :: !(x in A <==> x%2 == 0))
		ensures !(exists x :: x in A <==> x%2 == 0) <==> (forall x :: !(x in A <==> x%2 == 0))
		// <==>? (exists y :: y in A && y%2 != 0)
	{}

}