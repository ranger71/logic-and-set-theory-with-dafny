include "definitions_until_lecture09.dfy"

module Exam_2022_A {
	import opened SetTheory_Definitions

	// ((A /\ (not B)) \/ B) <--> (A \/ B)
	lemma Q1__PROOF_BY_TRUTH_TABLE__in_a_comment(A: bool, B: bool)
		ensures ((A && !B) || B) <==> (A || B)
	{
	/*
	A	B	!B	(A && !B)	((A && !B) || B)	(A || B)	(((A && !B) || B) <==> (A || B))
	F	F	T 	F        	F               	F       	T
	F	T	F 	F        	T               	T       	T
	T	F	T 	T        	T               	T       	T
	T	T	F 	F        	T               	T       	T
	*/
	}

	ghost function f2a(): BinaryRelation<int, int>
	{
		iset{(4,7), (5,4), (5,5), (5,6), (6,6), (6,8), (7,5), (8,6), (8,4)}
	}

	ghost function f2b(): BinaryRelation<int, int> // complete the definition here...
	{
		iset{(4,7), (5,4), (6,8), (8,6), (8,4)}
	}

	ghost function f2c(): BinaryRelation<int, int> // complete the definition here...
	{
		iset{(7,6), (7,7), (5,7)} // adding either (6,5) or (5,7) is fine too (but not both)
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

	ghost function f3a(): BinaryRelation<int, int>
	{
		iset{(7,6), (7,5), (6,6), (6,4), (3,7), (4,6), (4,5), (5,3)}
	}

	ghost function f3b(): BinaryRelation<int, int> // complete the definition here...
	{
		iset{(3,3), (3,5), (4,4), (5,5), (5,7), (7,3), (7,7)}
	}

	ghost function f3c(): BinaryRelation<int, int> // complete the definition here...
	{
		iset{(7,6), (4,5)} // could also "remove" (4,6), (6,4)
	}

	ghost const A3: iset<int> := iset{3,4,5,6,7}
	ghost const R3: BinaryRelation<int, int> := (f3a() + f3b()) - f3c()

	method Q3()
	{
		assert f3a() !! f3b();
		assert f3c() < f3a();
		assert EquivalenceRelation(R3, A3);
		assert EquivalenceClassOf(5, A3, R3) == iset{3,5,7};
	}

	ghost const R4a := iset{(3,3), (2,2), (1,1), (3,2), (2,1)}
	ghost const R4b := iset{(3,3), (2,2), (1,1), (3,2)}
	ghost const R4c := iset{(3,3), (2,2), (1,1), (3,1), (1,3)}
	ghost const R4d := iset{(3,2), (3,1), (2,1)}

	ghost const A4: iset<int> := iset{1,2,3}

	ghost const AllR4 := {R4a, R4b, R4c, R4d}

	ghost function f4a(): BinaryRelation<int, int> // complete the definition here...
	{
		R4b
	}

	ghost function f4b(): BinaryRelation<int, int> // complete the definition here...
	{
		R4d
	}

	ghost function f4c(): BinaryRelation<int, int> // complete the definition here...
	{
		R4a
	}

	ghost function f4d(): BinaryRelation<int, int> // complete the definition here...
	{
		R4c
	}

	method Q4()
	{
		assert {f4a(), f4b(), f4c(), f4d()} <= AllR4;
		assert IsPartialOrder(f4a(), A4);
		assert !Reflexive(f4b(), A4);
		assert !Transitive(f4c());
		assert !AntiSymmetric(f4d());
	}

	ghost const A5 := iset{2,3,4,5}
	ghost const R5 := iset{(2,2), (2,3), (3,3), (4,4), (4,5), (5,5)}

	ghost const R5a := iset{(4,2), (4,3), (5,2), (5,3), (5,4)}
	ghost const R5b := iset{(3,4), (5,2)}
	ghost const R5c := iset{(4,2), (4,3), (5,2), (5,3)}
	ghost const R5d := iset{(3,4)}

	ghost const AllR5 := {R5+R5a, R5+R5b, R5+R5c, R5+R5d}

	ghost function f5a(): BinaryRelation<int, int> // complete the definition here...
	{
		R5+R5b // and could reverse with the deinition of f5b() as both are expected to be !Transitive
	}

	ghost function f5b(): BinaryRelation<int, int> // complete the definition here...
	{
		R5+R5d
	}

	ghost function f5c(): BinaryRelation<int, int> // complete the definition here...
	{
		R5+R5a
	}

	ghost function f5d(): BinaryRelation<int, int> // complete the definition here...
	{
		R5+R5c
	}

	method Q5()
	{
		assert {f5a(), f5b(), f5c(), f5d()} == AllR5;
		assert !Transitive(f5a());
		assert !Transitive(f5b());
		assert !AntiSymmetric(f5c());
		assert IsTotalOrder(f5d(), A5);
	}

	ghost const R6a := iset{(1,4), (1,5), (2,6), (3,7)}
	ghost const R6b := iset{(1,4), (2,5), (3,7)}
	ghost const R6c := iset{(1,7), (2,5), (3,7)}
	ghost const R6d := iset{(4,4), (5,5), (6,6), (7,7)}

	ghost const A6a: iset<int> := iset{1,2,3}
	ghost const A6b: iset<int> := iset{4,5,6,7}

	ghost const AllR6 := {R6a, R6b, R6c, R6d}

	ghost function f6a(): BinaryRelation<int, int> // complete the definition here...
	{
		R6d
	}

	ghost function f6b(): BinaryRelation<int, int> // complete the definition here...
	{
		R6a
	}

	ghost function f6c(): BinaryRelation<int, int> // complete the definition here...
	{
		R6c // not being a valid function, R6a could have been correct here, yet it is the only relation that answers f6b() correctly
	}

	ghost function f6d(): BinaryRelation<int, int> // complete the definition here...
	{
		R6b
	}

	method Q6()
	{
		assert {f6a(), f6b(), f6c(), f6d()} == AllR6;
		assert Domain(f6a()) != A6a;
		assert !ValidFunction(f6b());
		assert !InjectiveFunction(f6c());
		assert Domain(f6d()) == A6a && Range(f6d()) <= A6b;
		assert InjectiveFunction(f6d());
	}

	ghost const R7a := iset{(1,5), (2,6), (3,7)}
	ghost const R7b := iset{(1,5), (2,5), (3,7), (4,6)}
	ghost const R7c := iset{(1,5), (1,6), (1,7)}
	ghost const R7d := iset{(1,7), (2,6), (3,5), (4,4)}

	ghost const A7a: iset<int> := iset{1,2,3,4}
	ghost const A7b: iset<int> := iset{5,6,7}

	ghost const AllR7 := {R7a, R7b, R7c, R7d}

	ghost function f7a(): BinaryRelation<int, int> // complete the definition here...
	{
		R7d // solution
	}

	ghost function f7b(): BinaryRelation<int, int> // complete the definition here...
	{
		R7a // solution
			// R7c here would be correct by itself but is needed in f7d (as the only !ValidFunction)
	}

	ghost function f7c(): BinaryRelation<int, int> // complete the definition here...
	{
		R7b // solution
	}

	ghost function f7d(): BinaryRelation<int, int> // complete the definition here...
	{
		R7c // solution
	}

	// prove by making an assignment to the result parameters only
	lemma Lemma7() returns (x: int, y: int)
		ensures (x,y) in f7a() && y !in A7b
	{
		x, y := 4, 4; // solution
	}

	method Q7()
	{
		assert {f7a(), f7b(), f7c(), f7d()} == AllR7;
		assert !(Range(f7a()) <= A7b) by {
			var x,y := Lemma7();
			assert (x,y) in f7a() && y !in A7b;
		}
		assert Domain(f7b()) != A7a;
		assert SurjectiveFunction(f7c(), A7a, A7b);
		assert !ValidFunction(f7d());
	}

	ghost const A8 := iset x: int | x < 4
	ghost const B8 := iset y: int | y > -4

	ghost const F8a := iset x, y | x in A8 && y in B8 && x+y == 0 :: (x,y)
	ghost const F8b := iset x, y | x in A8 && y in B8 && x-y == 0 :: (x,y)

	ghost function goodF8(): BinaryRelation<int, int> // complete the definition here...
	{
		F8a // solution
	}

	ghost function badF8(): BinaryRelation<int, int> // complete the definition here...
	{
		F8b // solution
	}

	// goal: provide a complete proof for this lemma
	lemma LemmaGoodF8() returns (F: BinaryRelation<int, int>)
		ensures F == goodF8()
		ensures ValidFunctionDomain(F, A8)
		ensures Range(F) <= B8
		ensures BijectiveFunction(F, A8, B8)
	{ // a partial solution
		F := goodF8();
		assert ValidFunctionDomain(F, A8) by {
			forall x | x in A8 ensures x in Domain(F) {
				assert x < 4;
				var y := -x;
				assert y > -4;
				assert y in B8;
				assert (x,y) in F;
			}
		}
		assert Range(F) <= B8;
		assert BijectiveFunction(F, A8, B8) by {
			assert InjectiveFunction(F);
			assert SurjectiveFunction(F, A8, B8) by {
				forall y | y in B8 ensures exists x :: x in A8 && (x,y) in F {
					assert y > -4;
					var x' := -y;
					assert x' < 4;
					assert x' in A8;
				}
			}
		}
	}

	// goal: provide a complete proof for this lemma too
	lemma LemmaBadF8(F: BinaryRelation<int, int>)
		requires F == badF8()
		ensures A8 != Domain(F)
	{ // solution
		var x := -4;
		forall y | y in B8 ensures (x, y) !in F {
			assert y > -4;
			assert x != y;
			assert x-y != 0;
			assert (x,y) !in F;
		}
		assert x in A8 && x !in Domain(F);
	}

	method Q8() {
		assert {goodF8(), badF8()} == {F8a, F8b};
		var F := badF8();
		assert A8 != Domain(F) by {
			LemmaBadF8(F);
		}
		assert CardinallyEquivalentSets(A8, B8) by {
			var F := LemmaGoodF8();
			assert ValidFunctionDomain(F, A8);
			assert Range(F) <= B8;
			assert BijectiveFunction(F, A8, B8);
		}
	}
}