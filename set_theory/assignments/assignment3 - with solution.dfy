include "definitions_until_lecture09.dfy"

// exercise 1: total order
ghost const A1: iset<int> := iset{3,4,5}
ghost const R1: BinaryRelation<int, int> := iset{(3,3), (4,4), (4,5), (5,5)}

ghost const R1a: BinaryRelation<int, int> := iset{(3,4), (5,3)}
ghost const R1b: BinaryRelation<int, int> := iset{(3,4)}
ghost const R1c: BinaryRelation<int, int> := iset{(3,4), (3,5), (4,3), (5,3), (5,4)}
ghost const R1d: BinaryRelation<int, int> := iset{(4,3), (5,3)}

ghost const AllR1 := {R1+R1a, R1+R1b, R1+R1c, R1+R1d}

ghost function f1a(): BinaryRelation<int, int> {
	R1+R1d // solution
}

ghost function f1b(): BinaryRelation<int, int> {
	R1+R1a // solution
}

ghost function f1c(): BinaryRelation<int, int> {
	R1+R1c // solution
}

ghost function f1d(): BinaryRelation<int, int> {
	R1+R1b // solution
}

method {:verify true} Q1() {
	assert f1a() in AllR1 && f1b() in AllR1 && f1c() in AllR1 && f1d() in AllR1;
	assert f1b() != f1d();
	assert IsTotalOrder(f1a(), A1);
	assert !IsTotalOrder(f1b(), A1) by { assert !Transitive(f1b()); }
	assert !IsTotalOrder(f1c(), A1) by { assert !AntiSymmetric(f1c()); }
	assert !IsTotalOrder(f1d(), A1) by { assert !Transitive(f1d()); }
}

// exercise 2: injective functions
ghost const R2a: BinaryRelation<int, int> := iset{(1,5), (1,6), (2,4), (3,7), (4,8)}
ghost const R2b: BinaryRelation<int, int> := iset{(1,8), (2,8), (3,8), (4,8)}
ghost const R2c: BinaryRelation<int, int> := iset{}
ghost const R2d: BinaryRelation<int, int> := iset{(1,4), (2,5), (3,7), (4,8)}

ghost const A2a: iset<int> := iset{1,2,3,4}
ghost const A2b: iset<int> := iset{4,5,6,7,8}

ghost const AllR2 := {R2a, R2b, R2c, R2d}

ghost function f2a(): BinaryRelation<int, int> {
	R2c // solution
}

ghost function f2b(): BinaryRelation<int, int> {
	R2a // solution
}

ghost function f2c(): BinaryRelation<int, int> {
	R2b // solution
}

ghost function f2d(): BinaryRelation<int, int> {
	R2d // solution
}

method {:verify true} Q2() {
	assert f2a() in AllR2 && f2b() in AllR2 && f2c() in AllR2 && f2d() in AllR2;
	assert Domain(f2a()) != A2a;
	assert !ValidFunction(f2b());
	assert !InjectiveFunction(f2c());
	assert Domain(f2d()) == A2a && Range(f2d()) <= A2b && InjectiveFunction(f2d());
}

// exercise 3: surjective functions
ghost const R3a: BinaryRelation<int, int> := iset{(4,1), (5,2), (6,2), (7,3), (8,0)}
ghost const R3b: BinaryRelation<int, int> := iset{(4,3), (4,2), (4,1), (4,0)}
ghost const R3c: BinaryRelation<int, int> := iset{(5,3), (6,2), (7,1), (8,0)}
ghost const R3d: BinaryRelation<int, int> := iset{(4,1), (5,2), (6,3), (7,4), (8,0)}

ghost const A3a: iset<int> := iset{4,5,6,7,8}
ghost const A3b: iset<int> := iset{0,1,2,3}

ghost const AllR3 := {R3a, R3b, R3c, R3d}

ghost function f3a(): BinaryRelation<int, int> {
	R3d // solution
}

ghost function f3b(): BinaryRelation<int, int> {
	R3c // solution
}

ghost function f3c(): BinaryRelation<int, int> {
	R3a // solution
}

ghost function f3d(): BinaryRelation<int, int> {
	R3b // solution
}

method {:verify true} Q3() {
	assert {f3a(), f3b(), f3c(), f3d()} == AllR3;
	assert !(Range(f3a()) <= A3b) by { assert 4 in Range(f3a())-A3b; }
	assert Domain(f3b()) != A3a;
	assert SurjectiveFunction(f3c(), A3a, A3b);
	assert !ValidFunction(f3d());
}

// preparation for exercise 4: example of proving cardinal equivalence
ghost const A4 := iset x: int | x > 5
ghost const B4 := iset x: int | x < 5

ghost const F4a := iset x, y | x in A4 && y in B4 && x == 10-y :: (x,y)
ghost const F4b := iset x, y | x in A4 && y in B4 && x == 9-y :: (x,y)

ghost function goodF4(): BinaryRelation<int, int> {
	F4a // solution
}

ghost function badF4(): BinaryRelation<int, int> {
	F4b // solution
}

lemma {:verify true} LemmaGoodF4() returns (F: BinaryRelation<int, int>)
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

method PreparationForQ4() {
	assert {goodF4(), badF4()} == {F4a, F4b};
	var F := badF4();
	assert ValidFunction(F) && A4 == Domain(F) && Range(F) <= B4 && !SurjectiveFunction(F, A4, B4) by {
		LemmaBadF4(F);
	}
	assert CardinallyEquivalentSets(A4, B4) by {
		var F := LemmaGoodF4();
		assert ValidFunctionDomain(F, A4) && Range(F) <= B4 && BijectiveFunction(F, A4, B4);
	}
}

// exercise 4: proving cardinal equivalence
ghost const C4 := iset x: int | x < 0
ghost const D4 := iset y: int | y > 3

ghost const G4a := iset x, y | x in C4 && y in D4 && 4-x == y :: (x,y)
ghost const G4b := iset x, y | x in C4 && y in D4 && 3-x == y :: (x,y)

ghost function goodG4(): BinaryRelation<int, int> {
	G4b // solution
}

ghost function badG4(): BinaryRelation<int, int> {
	G4a // solution
}

lemma {:verify true} LemmaGoodG4() returns (F: BinaryRelation<int, int>)
	ensures F == goodG4()
	ensures ValidFunctionDomain(F, C4) && Range(F) <= D4 && BijectiveFunction(F, C4, D4)
{ // a partial solution - see a more complete solution in tutorial09
	F := goodG4();
	assert ValidFunctionDomain(F, C4) by {
		forall x | x in C4 ensures x in Domain(F) {
			assert x < 0;
			var y := 3-x;
			assert y > 3;
			assert y in D4;
			assert (x,y) in F;
		}
	}
	assert Range(F) <= D4;
	assert BijectiveFunction(F, C4, D4) by {
		assert InjectiveFunction(F);
		assert SurjectiveFunction(F, C4, D4) by {
			forall y | y in D4 ensures exists x :: x in C4 && (x,y) in F {
				assert y > 3;
				var x' := 3-y;
				assert x' < 0;
				assert x' in C4;
			}
		}
	}
}

lemma LemmaBadG4(F: BinaryRelation<int, int>)
	requires F == badG4()
	ensures ValidFunction(F) && C4 == Domain(F) && Range(F) <= D4
	ensures !SurjectiveFunction(F, C4, D4)
{ // a partial solution - see a more complete solution in tutorial09
	assert ValidFunction(F);
	assert C4 == Domain(F) by {
		assert C4 <= Domain(F) by {
			forall x | x in C4 ensures x in Domain(F) {
				assert x < 0;
				var y := 4-x;
				assert y > 4;
				assert y in D4;
				assert (x,y) in F;
			}
		}
		assert C4 >= Domain(F);
	}
	assert Range(F) <= D4;
	assert !SurjectiveFunction(F, C4, D4) by {
		var y := 4;
		assert 4-y == 0 && 0 !in C4;
		assert y !in Range(F);
		assert !SurjectiveFunction'(F, C4, D4);
		EquivalentSurjectiveDefinitions(F, C4, D4);
	}
}

method Q4() {
	assert {goodG4(), badG4()} == {G4a, G4b};
	var F := badG4();
	assert ValidFunction(F) && C4 == Domain(F) && Range(F) <= D4 && !SurjectiveFunction(F, C4, D4) by {
		LemmaBadG4(F);
	}
	assert CardinallyEquivalentSets(C4, D4) by {
		var F := LemmaGoodG4();
		assert ValidFunctionDomain(F, C4) && Range(F) <= D4 && BijectiveFunction(F, C4, D4);
	}
}