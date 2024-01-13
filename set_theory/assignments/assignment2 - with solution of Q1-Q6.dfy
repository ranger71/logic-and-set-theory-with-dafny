include "definitions_until_lecture09.dfy"

ghost const R1 := iset a,b | a == 4 || a+b == 4 :: (a,b)

ghost function f1a(): (int,int) {
	(4,0) // solution
}

ghost function f1b(): (int,int) {
	(2,3) // solution
}

ghost function f1c(): (int,int) {
	(4,3) // solution
}

ghost function f1d(): (int,int) {
	(1,3) // solution
}

ghost const AllPairs1 := {f1a(), f1b(), f1c(), f1d()}

method {:verify true} Q1()
{
	assert |AllPairs1| == 4;
	var p := f1a();
	assert p in R1 by { assert p.0 == 4 && p.0 + p.1 == 4; }
	p := f1b();
	assert p !in R1;
	p := f1c();
	assert p.0+p.1 != 4;
	assert p in R1 by { assert p.0 == 4; }
	p := f1d();
	assert p.0 != 4;
	assert p in R1 by { assert p.0 + p.1 == 4; }
}

// תרגיל 2: יחסים בינאריים, יחס על קבוצה, רפלקסיביות, טרנזיטיביות וסימטריה
ghost function f2a(): BinaryRelation<int, int> {
	iset{(1,1), (1,2), (1,5), (2,2), (2,4), (3,1), (4,2), (4,5), (5,3)}
}

ghost function f2b(): BinaryRelation<int, int> {
	iset{(1,5), (2,4), (4,2), (4,5), (5,3)} // solution
}

ghost function f2c(): BinaryRelation<int, int> {
	iset{(3,2), (3,3)} // solution
}

ghost const A2: iset<int> := iset{1,2,3}
ghost const R2: BinaryRelation<int, int> := (f2a() - f2b()) + f2c()

method {:verify true} Q2() {
	assert f2a() !! f2c();
	assert f2b() < f2a();
	assert forall p :: p in f2b() ==> p.0 !in A2 || p.1 !in A2;
	assert RelationOn(R2, A2);
	assert Reflexive(R2, A2);
	assert Transitive(R2);
	assert !EquivalenceRelation(R2, A2) by {
		assert !Symmetric(R2);
	}
}

// exercise 3: equivalence relation + equivalence classes
ghost function f3a(): BinaryRelation<int, int> {
	iset{(1,1), (1,2), (1,5), (2,2), (2,4), (3,1), (4,2), (4,5), (5,3)}
}

ghost function f3b(): BinaryRelation<int, int> {
	iset{(1,2), (4,5)} // solution
}

ghost function f3c(): BinaryRelation<int, int> {
	iset{(1,3), (3,3), (3,5), (4,4), (5,1), (5,5)} // solution
}

ghost const A3: iset<int> := iset{1,2,3,4,5}
ghost const R3: BinaryRelation<int, int> := (f3a() - f3b()) + f3c()

method {:verify true} Q3() {
	assert f3a() !! f3c();
	assert f3b() < f3a();
	assert EquivalenceRelation(R3, A3);
	assert EquivalenceClassOf(1, A3, R3) == iset{1,3,5};
}

// exercise 4: partial order
ghost const R4a: BinaryRelation<int, int> := iset{(5,5), (5,3), (4,4), (3,5), (3,3), (2,2)}
ghost const R4b: BinaryRelation<int, int> := iset{(5,5), (5,3), (4,4), (3,3), (3,2), (2,2)}
ghost const R4c: BinaryRelation<int, int> := iset{}
ghost const R4d: BinaryRelation<int, int> := iset{(5,5), (5,4), (4,4), (3,3), (3,2), (2,2)}

ghost const A4: iset<int> := iset{2,3,4,5}

ghost const AllR4 := {R4a, R4b, R4c, R4d}

ghost function f4a(): BinaryRelation<int, int> {
	R4d // solution
}

ghost function f4b(): BinaryRelation<int, int> {
	R4c // solution
}

ghost function f4c(): BinaryRelation<int, int> {
	R4b // solution
}

ghost function f4d(): BinaryRelation<int, int> {
	R4a // solution
}

method {:verify true} Q4() {
	assert f4a() in AllR4 && f4b() in AllR4 && f4c() in AllR4 && f4d() in AllR4;
	assert IsPartialOrder(f4a(), A4);
	assert !IsPartialOrder(f4b(), A4) by { assert !Reflexive(f4b(), A4); }
	assert !IsPartialOrder(f4c(), A4) by { assert !Transitive(f4c()); }
	assert !IsPartialOrder(f4d(), A4) by { assert !AntiSymmetric(f4d()); }
}

// exercise 5: binary relations
ghost predicate P5a(x: int, y: int) {
	x%2 == 0 && y == x+3 /// the x%2 == 0 is possibly not necessary
}

ghost predicate P5b(x: int) {
	true
}

ghost predicate P5c(x: int, y: int) {
	x == 1 && y == 4
}

ghost const R5a: BinaryRelation<int,int> := iset a,b | P5a(a,b) :: (a,b)
ghost const R5b: BinaryRelation<int,int> := iset a,b | P5b(a) && P5b(b) :: (a,b)
ghost const R5c: BinaryRelation<int,int> := iset a,b | P5c(a,b) :: (a,b)
ghost const R5d := R5a * (R5b - R5c)

lemma L5() returns (x: int)
	ensures (x,x+3) !in R5d
{
	x := 1;
}

method {:verify true} Q5() {
	assert R5a * R5c == iset{};
	assert forall x: int :: x%2 == 0 ==> (x, x+3) in R5d;
	var a := L5();
	assert exists x: int :: (x, x+3) !in R5d by { assert (a, a+3) !in R5d; }
}

// exercise 6: a detailed formal proof
lemma Q6_InverseDomain<T(!new)>(R: BinaryRelation<T,T>, InverseR: BinaryRelation<T,T>, A: iset<T>)
	requires pre1: RelationOn(R, A)
	requires pre2: InverseR == InverseRelation(R)
	ensures Range(R) == Domain(InverseR)
{
	// <=
	forall b | b in Range(R) ensures b in Domain(InverseR){
		assert 3: b in Range(R);
		assert b in Domain(InverseR) by {reveal pre1,pre2,3;}
	}
	// >=
	forall b | b in Domain(InverseR) ensures b in Range(R){
		assert 4: b in Domain(InverseR);
		assert b in Range(R) by {reveal pre1,pre2,4;}
	}
}

// exercise 7: a detailed formal proof on partial orders
lemma Q7_GE_IsPartialOrder(R: BinaryRelation<int,int>, A: iset<int>)
    requires pre1: RelationOn(R, A)
    requires pre2: R == Q7_GE_Relation(A)
	 ensures IsPartialOrder(R, A)

ghost function Q7_GE_Relation(A: iset<int>): BinaryRelation<int,int> {
	iset x,y | x in A && y in A && x >= y :: (x,y)
}
