/*
Tutorial 7: equivalence class + partial order
*/
include "../lectures/lecture07.dfy"

method {:verify true} Q7a()
{
	ghost var A := iset{0,1,2,3,4,5,6};
	ghost var a4_R := iset{1,4,6};
	ghost var R1 := iset{(1,4), (1,6), (2,2), (3,3), (3,5), (4,4), (4,6), (5,3), (6,1), (6,4)};
	ghost var R2a := iset{(0,0), (1,1), (5,5), (6,6)}; // for reflexivity
	ghost var R2b := iset{(4,1)}; // for symmetry
	ghost var R2c := iset{}; // R1+R2a_R2b is already transitive
	ghost var R2 := R2a+R2b+R2c;
	ghost var R3 := R1+R2;
	assert EquivalenceRelation(R3, A);
	assert EquivalenceClassOf(4, A, R3) == a4_R == iset{1,4,6};
}

/*
{(4,4), (4,3), (3,3), (2,2), (2,1), (1,1)}

is this a partial order on {1,2,3,4}?

Yes!

And this?
{(4,4), (3,3), (3,2), (2,2), (2,1), (1,1)} // not transitive: missing (3,1)

And this?
{} // not reflexive on {1,2,3,4}

*/
method {:verify true} Q7b() // added after the tutorial (following the contents of the comment above, as solved during the tutorial):
{
	ghost var A := iset{1,2,3,4};
	ghost var R1 := iset{(4,4), (4,3), (3,3), (2,2), (2,1), (1,1)};
	assert IsPartialOrder(R1, A) by {
		assert RelationOn(R1, A);
		assert Transitive(R1) && Reflexive(R1, A) && AntiSymmetric(R1);
	}
	ghost var R2 := iset{(4,4), (3,3), (3,2), (2,2), (2,1), (1,1)};
	assert !IsPartialOrder(R2, A) by {
		assert !Transitive(R2) by {
			var a, b, c := 3, 2, 1;
			assert (3,2) in R2;
			assert (2,1) in R2;
			assert (3,1) !in R2;
		}
	}
	ghost var R3: BinaryRelation<int, int> := iset{};
	assert !IsPartialOrder(R3, A) by {
		assert !Reflexive(R3, A) by {
			assert (1,1) !in R3;
		}
	}
}
