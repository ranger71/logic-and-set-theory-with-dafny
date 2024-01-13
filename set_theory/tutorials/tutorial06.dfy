/*
	tutorial 6: more on binary relations: reflexivity, symmetry, equivalence relations, equivalence classes
*/
include "../lectures/lecture05.dfy"

ghost predicate Reflexive<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires RelationOn(R, A)
{
    forall a :: a in A ==> (a,a) in R
}
ghost predicate Symmetric<T(!new)>(R: BinaryRelation<T,T>) { forall a: T, b: T :: (a,b) in R <==> (b, a) in R }
ghost predicate EquivalenceRelation<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires RelationOn(R, A)
{
    Transitive(R) && Reflexive(R, A) && Symmetric(R)
}

ghost const A_T6a := iset{1,2,3,4}
ghost const A_T6b := A_T6a - iset{4} // == iset{1,2,3}
ghost const A_T6c := A_T6b - iset{3} // == iset{1,2}
ghost const R_T6a := iset{(1,1), (1,2), (2,1), (2,2), (3,3)}
ghost const R_T6c := R_T6a - iset{(3,3)} // == iset{(1,1), (1,2), (2,1), (2,2)}

method M_T6a()
{
	assert RelationOn(R_T6a, A_T6a);
	assert Transitive(R_T6a);
	assert Symmetric(R_T6a);
	assert !Reflexive(R_T6a, A_T6a) by { assert (4,4) !in R_T6a; }

	assert RelationOn(R_T6a, A_T6b);
	assert EquivalenceRelation(R_T6a, A_T6b) by {
		assert Transitive(R_T6a);
		assert Symmetric(R_T6a);
		assert Reflexive(R_T6a, A_T6b);
	}

	//assert !EquivalenceRelation(R_T6a, A_T6c); // we are NOT allowed to call this ghost predicate on such parameter since the precondition ("requires" condition) does not hold:
	assert !RelationOn(R_T6a, A_T6c) by { assert (3,3) in R_T6a && 3 !in A_T6c; }

	assert EquivalenceRelation(R_T6c, A_T6c);
}

ghost function EquivalenceClassOf<T>(a: T, A: iset<T>, R: BinaryRelation<T,T>): iset<T>
    requires a in A && RelationOn(R, A) && EquivalenceRelation(R, A)
{
    iset x | x in A && (a,x) in R
}

method M_T6b()
{
	assert EquivalenceClassOf(1, A_T6b, R_T6a) == iset{1, 2};
	assert EquivalenceClassOf(2, A_T6b, R_T6a) == iset{1, 2};
	assert EquivalenceClassOf(3, A_T6b, R_T6a) == iset{3};
	//assert EquivalenceClassOf(4, A_T6b, R_T6a) == iset{}; //  precondition might not hold: 4 !in A_T6b
}
