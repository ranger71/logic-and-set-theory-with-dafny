/*
	tutorial 5: binary relations, transitivity, and more on negation of quantifiers (proof by calculation)
*/
include "../lectures/lecture05.dfy"

ghost const T1: BinaryRelation<nat,nat> := iset{(1, 1), (1, 2), (2, 1), (2, 2), (3, 3)}
ghost const AllNaturalNumbers := iset n: int | n >= 0
ghost const PositiveIntegers := iset n: int | n >= 1
ghost const PositiveEvenIntegers := iset n: int | n >= 1 && n % 2 == 0

ghost const T2: BinaryRelation<nat,nat> := T1 + iset{(2,3)}

method T5a()
{
	assert RelationOn(T1, iset{1,2,3});
	assert !RelationOn(T1, iset{1,2,4});
	assert RelationOn(T1, AllNaturalNumbers);
	assert RelationOn(T1, PositiveIntegers);
	assert !RelationOn(T1, PositiveEvenIntegers);

	assert Transitive(T1);
	assert 1: NonTransitive(T2) by {
		var a, b, c := 1, 2, 3;
		assert (1, 2) in T2;
		assert (2, 3) in T2;
		assert (1, 3) !in T2;
	}
	assert !Transitive(T2) by {
		assert NonTransitive(T2) by { reveal 1; }
		NonTransitivityLemma(T2);
	}
}

/*
for any R we have !Transitive(R) == NonTransitive(R)
*/
lemma NonTransitivityLemma<T(!new)>(R: BinaryRelation<T, T>)
	ensures !Transitive(R) == NonTransitive(R)
{
	calc {
		!Transitive(R);
	== // by definition
		!forall a, b, c :: (a,b) in R && (b,c) in R ==> (a,c) in R;
	== // negation of quantifiers
		exists a, b, c :: !((a,b) in R && (b,c) in R ==> (a,c) in R);
	== { assert forall P,Q :: (!P || Q) <==> (P ==> Q); } // see truth table in lecture02.dfy
		exists a, b, c :: !(!((a,b) in R && (b,c) in R) || (a,c) in R);
	== // De Morgan (on the outer negation, completed after the tutorial: during the session, I was wrong to perform this step on the inner negation)
		exists a, b, c :: !!((a,b) in R && (b,c) in R) && (a,c) !in R;
	== // remove double negation
		exists a, b, c :: (a,b) in R && (b,c) in R && (a,c) !in R;
	== // by definition
		NonTransitive(R);
	}
}