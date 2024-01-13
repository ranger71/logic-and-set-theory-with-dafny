/*
lecture 5

- lemma with result parameters: existentially (instead of universally) quantified
	- useful also as a second approach for proof by contradiction (with the returned values acting as a counterexample)
	- more on the negation of quantifiers
- introduction to binary relations and functions
	- ordered pairs
	- representing a binary relation as a (possibly infinite) set of pairs
	- a first property of relations: transitivity (leading with reflexivity and summetry next week to the definition of equivalence classes)
*/

/*
a lemma that returns values speaks of existential quantification (instead of universal quantification):

***there exist*** two sets A,B for which
if for any element a, a is not a member of A,
and if for any element b, b is not a member of B,
then the sets A and B are equal.
*/
lemma EmptySets'() returns (A: set, B: set)
	ensures (forall a :: a !in A) && (forall b :: b !in B) ==> A == B

lemma SquareOfNaturalNumbersIsMonotonic(a: nat, b: nat)
	requires a <= b
	ensures a*a <= b*b

lemma SquareOfIntegersIsNotMonotonic() returns (a: int, b: int)
	ensures !(a <= b ==> a*a <= b*b)
{
	a, b := -10, 5;
	assert !(a <= b ==> a*a <= b*b) by {
		calc {
			!(a <= b ==> a*a <= b*b);
		== // substitution of a,b by their concrete values -10,5
			!(-10 <= 5 ==> (-10)*(-10) <= 5*5);
		==
			!(true ==> (-10)*(-10) <= 5*5);
		==
			!(true ==> 100 <= 25);
		==
			!(true ==> false);
		== // by definition of logical implication (the truth table from lecture 2)
			!(false);
		==
			true;
		}
	}
}

lemma SquareOfIntegersIsNotMonotonic'() returns (a: int, b: int)
	ensures (a <= b) && (a*a > b*b)
{
	a, b := SquareOfIntegersIsNotMonotonic();
}

method M5a()
{
	assert forall x, y :: 0 <= x <= y ==> x*x <= y*y by {
		forall x',y' | 0 <= x' <= y' ensures x'*x' <= y'*y' {
			assert x'*x' <= y'*y' by { SquareOfNaturalNumbersIsMonotonic(x', y'); }
		}
	}
	assert !forall x: int, y: int :: x <= y ==> x*x <= y*y by {
		assert exists x': int, y': int :: x' <= y' && x'*x' > y'*y' by {
			var x'', y'' := SquareOfIntegersIsNotMonotonic'();
			assert x'' <= y'' && x''*x'' > y''*y'';
		}
	}
	// one more way (by contradiction):
	assert !forall x: int, y: int :: x <= y ==> x*x <= y*y by {
		if forall x: int, y: int :: x <= y ==> x*x <= y*y // assumption (הנחה בשלילה)
		{
			assert 0: forall x: int, y: int :: x <= y ==> x*x <= y*y; // by the guard above
			// leading to contradiction:
			var x', y' := SquareOfIntegersIsNotMonotonic'();
			assert 1: x' <= y'; // from the lemma
			assert 2: x'*x' <= y'*y' by { reveal 0,1; }
			assert 3: x'*x' > y'*y'; // from the lemma too
			assert false by { reveal 2,3; } // contradiction
		}
	}
}

// introduction to binary relations and functions

// ordered pairs: in mathematics it is common to write order pais using angular brackets <5,6>
const s1 := {5,6} // a set (the order does NOT matter)
const p1 := (5,6) // an ordered pair

method M5b()
{
	assert s1 == {6,5} == {5,6,5};
	assert p1 == (5,6) != (6,5);
	assert 5 == p1.0;
	assert 6 == p1.1;
}

lemma EqualityOfOrderedPairs<T1, T2>(p1: (T1, T2), p2: (T1, T2))
	ensures p1 == p2 <==> p1.0 == p2.0 && p1.1 == p2.1
{}

const R1: set<(int,int)> := {(5,5), (5,6), (5,7), (6,6), (6,9)}
const R2: iset<(int,int)> := iset{(5,5), (5,6), (5,7), (6,6), (6,9)}

type BinaryRelation<!T1(==),!T2(==)> = iset<(T1, T2)>

ghost const LessThanOrEqual_On_Integers: BinaryRelation<int, int> := iset x, y | x <= y :: (x, y)
ghost const LessThanOrEqual_On_Integers': BinaryRelation<int, int> := iset x, y | LessThanOrEqual(x, y) :: (x, y)
ghost const LessThanOrEqual_On_Integers'': BinaryRelation<int, int> := iset p: (int, int) | p.0 <= p.1
ghost const LessThanOrEqual_On_NaturalNumbers: BinaryRelation<nat, nat> := iset m: nat, n: nat | exists k: nat :: m+k == n :: (m,n)
ghost const LessThanOrEqual_On_NaturalNumbers': BinaryRelation<nat, nat> := iset m: nat, n: nat, k: nat | m+k == n :: (m,n)

predicate LessThanOrEqual(x: int, y: int) { x <= y }

method M5c()
{
	assert (5,8) in LessThanOrEqual_On_Integers;
	assert (5,5) in LessThanOrEqual_On_Integers;
	assert (5,0) !in LessThanOrEqual_On_Integers;
}

ghost const SquareOfIntegers: BinaryRelation<int, nat> := iset x, y | y == x*x :: (x, y)

const s2 := iset{5,7}
const s3 := s2-iset{5}

method M5d() {
	assert (-3, 9) in SquareOfIntegers;
	assert (3, 9) in SquareOfIntegers;
	assert iset{(0, 0), (1, 1), (2, 4), (3, 9), (4, 16)} <= SquareOfIntegers;
}

const R3 := iset{(5,7)}
const R4 := iset{(5,7), (7,5)}
const R5 := iset{(5,5), (5,7), (7,5)}
const R6 := iset{(5,5), (5,7), (7,5), (7,7)}

ghost predicate RelationOn<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>) {
	forall a,b :: (a,b) in R ==> a in A && b in A // forall p :: p in R ==> p.0 in A && p.1 in A
}

// a first property of binary relations: transitivity
ghost predicate Transitive<T(!new)>(R: BinaryRelation<T,T>) { forall a, b, c :: (a,b) in R && (b,c) in R ==> (a,c) in R }
ghost predicate NonTransitive<T(!new)>(R: BinaryRelation<T,T>) { exists a, b, c :: (a,b) in R && (b,c) in R && (a,c) !in R }
// see proof in tutorial05 that NonTransitive(R) == !Transitive(R) for any binary relation R

method M5e()
{
	assert RelationOn(R3, s2);
	assert s3 == iset{7};
	assert !RelationOn(R3, s3) by { assert (5, 7) in R3 && 5 !in s3; }

	assert Transitive(R3); // vacuously true
	assert NonTransitive(R4) by { // missing pairs: (5, 5) and (7,7)
		var a, b, c := 5, 7, 5;
		assert (5,7) in R4;
		assert (7,5) in R4;
		assert (5,5) !in R4;// and similarly (7,7) is missing too
	}
	assert NonTransitive(R5) by {
		// missing pair: (7,7)
		var a, b, c := 7, 5, 7;
		assert (7,5) in R5;
		assert (5,7) in R5;
		assert (7,7) !in R5;
	}
	assert Transitive(R6);
}
