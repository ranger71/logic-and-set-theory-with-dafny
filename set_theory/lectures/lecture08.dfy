/* Lecture 8: 

More on partial + total order

	- definition of total order
	- the inverse relation
	- union/intersection of partial orders: are they partial orders?

	Advanced/Extra:
	- lexicographic order

Functions

	- definition of a function as a special case of a binary relation
	- injective functions
	- surjective functions (onto)
	- bijective functions

	Advanced/Extra:
	- functions and equivalence relations
	- domain reduction
	- intersection and union of functions
	- lambda expressions: Dafny's builtin type for functions

*/

include "lecture07.dfy"

method M8a()
{
    assert {} <= {1} && {} <= {2} && {} <= {3};
    assert {1} <= {1,2} && {1} <= {1,3};
    assert {2} <= {1,2} && {2} <= {2,3};
    assert {3} <= {1,3} && {3} <= {2,3};
    assert {1,2} <= {1,2,3} && {1,3} <= {1,2,3} && {2,3} <= {1,2,3};
    var GE123 := iset{(1,1), (2,2), (3,3), (3,2), (3,1), (2,1)};
    assert IsTotalOrder(GE123, iset{1,2,3});
    assert !(RelationOn(GE123, iset{1,2}) && IsTotalOrder(GE123, iset{1,2}));
}

/*
the relation <= on (the infinite set of) natural numbers is a partial order;
it is actually even a linear/total order

Definition: a partial order with the additional property that for any a,b in A, a <=_R b or b <=_R a

And in such cases we say that that the elements of A are *comparable*
*/
ghost predicate IsTotalOrder<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires RelationOn(R, A)
{
    IsPartialOrder(R, A) && forall a,b :: a in A && b in A ==> (a,b) in R || (b,a) in R
}

// Here's an alternative definition:
ghost predicate IsTotalOrder'<T(!new)>(R: PartialOrder<T>, A: set<T>)
{
	forall a,b :: a in A && b in A ==> (a,b) in R || (b,a) in R
}

// inverse relation, R^-1
ghost function InverseRelation<T1(!new),T2(!new)>(R: BinaryRelation<T1,T2>): BinaryRelation<T2,T1> {
    iset x,y | x in Domain(R) && y in Range(R) && (x,y) in R :: (y,x)
}

lemma InverseElements<T(!new)>(R: BinaryRelation<T,T>, IR: BinaryRelation<T,T>, A: iset<T>)
    requires IR == InverseRelation(R)
    requires RelationOn(R, A)
    ensures RelationOn(IR, A)
// Exercise: write a full proof
{}

lemma InversePair<T1(!new),T2(!new)>(a: T1, b: T2, R: BinaryRelation<T1,T2>, IR: BinaryRelation<T2,T1>)
    requires IR == InverseRelation(R)
    ensures (a,b) in R <==> (b,a) in IR
{}

lemma {:verify false} InversePartialOrder<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires Pre: RelationOn(R, A) && IsPartialOrder(R, A)
    ensures RelationOn(InverseRelation(R), A) && IsPartialOrder(InverseRelation(R), A)
{
    var InverseR := InverseRelation(R);
    assert RelationOn(InverseR, A) by { reveal Pre; InverseElements(R, InverseR, A); }
    assert IsPartialOrder(InverseR, A) by {
        assert Reflexive(InverseR, A) by {
            forall a | a in A ensures (a,a) in InverseR {
                assert aa: (a,a) in R by { reveal Pre; assert Reflexive(R, A); }
                assert (a,a) in InverseR by { reveal aa; InversePair(a,a,R,InverseR); }
            }
        }
        assert Transitive(InverseR) by {
            forall a,b,c | iset{a,b,c} <= A && (a,b) in InverseR && (b,c) in InverseR ensures (a,c) in InverseR {
                assert ba: (b,a) in R by { assert (a,b) in InverseR; InversePair(b,a,R,InverseR); }
                assert cb: (c,b) in R by { assert (b,c) in InverseR; InversePair(c,b,R,InverseR); }
                assert ca: (c,a) in R by {  reveal cb,ba,Pre; assert Transitive(R); }
                assert (a,c) in InverseR by { reveal ca; InversePair(c,a,R,InverseR); }
            }
        }
        assert AntiSymmetric(InverseR) by {
            forall a,b | iset{a,b} <= A && (a,b) in InverseR && (b,a) in InverseR ensures a == b {
                assert ba2: (b,a) in R by { assert (a,b) in InverseR; InversePair(b,a,R,InverseR); }
                assert ab2: (a,b) in R by { assert (b,a) in InverseR; InversePair(a,b,R,InverseR); }
                assert a == b by { reveal ab2,ba2,Pre; assert AntiSymmetric(R); }
            }
        }
    }
}

lemma {:verify false} InverseTotalOrder<T(!new)>(R: PartialOrder<T>, A: iset<T>)
    requires RelationOn(R, A) && IsTotalOrder(R, A)
    ensures var IR := InverseRelation(R); RelationOn(IR, A) && IsTotalOrder(IR, A)
{
    var IR := InverseRelation(R);
    assert IsPartialOrder(IR, A) by {
        InversePartialOrder(R, A);
    }
    forall a,b | a in A && b in A ensures (a,b) in IR || (b,a) in IR {
        assert (a,b) in R || (b,a) in R by { assert IsTotalOrder(R, A); }
        if (a,b) in R
        {
            assert (b,a) in IR by { assert (a,b) in R && IR == InverseRelation(R); }
        }
        else
        {
            assert (a,b) in IR by { assert (b,a) in R && IR == InverseRelation(R); }
        }
    }
}

/*
Union and intersection of partial orders:

Union might not be anti-symmetric (for example the union of R with the inverse of R);
the intersection, however, *is* a partial order
*/
lemma UnionOfPartialOrdersIsNotAlwaysPartialOrder() returns (R: BinaryRelation<int,int>, S: BinaryRelation<int,int>, A: iset<int>)
    ensures RelationOn(R, A) && IsPartialOrder(R, A)
    ensures RelationOn(S, A) && IsPartialOrder(S, A)
    ensures RelationOn(S, A) && !IsPartialOrder(R+S, A)
{
    R, S, A := iset{(1,1),(1,2),(2,2)}, iset{(1,1),(2,1),(2,2)}, iset{1,2};
    assert !AntiSymmetric(R+S) by { assert (1,2) in R+S && (2,1) in R+S && 1 != 2; }
}

lemma InterectionOfPartialOrdersIsPartialOrder<T(!new)>(R: BinaryRelation<T,T>, S: BinaryRelation<T,T>, A: iset<T>)
    requires PreR: RelationOn(R, A) && IsPartialOrder(R, A)
    requires PreS: RelationOn(S, A) && IsPartialOrder(S, A)
    ensures RelationOn(R*S, A) && IsPartialOrder(R*S, A)
{
    var RS := R*S;
    assert RelationOn(RS, A) by { reveal PreR,PreS; assert RS == R*S <= R; }
    assert IsPartialOrder(RS, A) by {
        assert Reflexive(RS, A) by {
            forall a | a in A ensures (a,a) in RS {
                assert aa: (a,a) in R by { reveal PreR; assert Reflexive(R, A); }
                assert aa2: (a,a) in S by { reveal PreS; assert Reflexive(S, A); }
                assert (a,a) in RS by { reveal aa,aa2; assert RS == R*S; }
            }
        }
        assert Transitive(RS) by {
            forall a,b,c | iset{a,b,c} <= A && (a,b) in RS && (b,c) in RS ensures (a,c) in RS {
                assert ab: (a,b) in R by { assert (a,b) in RS && RS <= R; }
                assert bc: (b,c) in R by { assert (b,c) in RS && RS <= R; }
                assert ac: (a,c) in R by { reveal ab,bc,PreR; assert Transitive(R); }
                assert ab2: (a,b) in S by { assert (a,b) in RS && RS <= S; }
                assert bc2: (b,c) in S by { assert (b,c) in RS && RS <= S; }
                assert ac2: (a,c) in S by { reveal ab2,bc2,PreS; assert Transitive(S); }
                assert (a,c) in RS by { reveal ac,ac2; assert RS == R*S; }
            }
        }
        assert AntiSymmetric(RS) by {
            forall a,b | iset{a,b} <= A && (a,b) in RS && (b,a) in RS ensures a == b {
                assert ab3: (a,b) in R by { assert (a,b) in RS; assert RS <= R; }
                assert ba3: (b,a) in R by { assert (b,a) in RS; assert RS <= R; }
                assert a == b by { reveal ab3,ba3,PreR; assert AntiSymmetric(R); }
            }
        }
    }
}

/*
Example for a partial (yet not total) order: the identity relation
*/
ghost function IdentityRelation<T>(A: iset<T>): BinaryRelation<T,T>
{
	iset a | a in A :: (a, a)
}

//lemma()

method M8b()
{
	var A := iset{1,2};
	var R := IdentityRelation(A);
	assert R == iset{(1, 1), (2, 2)};
	assert IsPartialOrder(R, A);
	assert !IsTotalOrder(R, A) by { var a, b := 1, 2; assert 1 in A && 2 in A; assert (a, b) !in R && (b, a) !in R; }
	//assert !AntiSymmetric(R+S) by { assert (1,2) in R+S && (2,1) in R+S && 1 != 2; }
}


// One more example for a partial order: lexicographic order
ghost function LexicographicOrder<T1(!new),T2(!new)>(R: BinaryRelation<T1,T1>, S: BinaryRelation<T2,T2>, A: iset<T1>, B: iset<T2>): BinaryRelation<(T1,T2),(T1,T2)>
    requires RelationOn(R, A) && IsPartialOrder(R, A)
    requires RelationOn(S, B) && IsPartialOrder(S, B)
{
    iset a1,b1,a2,b2 | a1 in A && a2 in A && b1 in B && b2 in B &&
        (((a1,a2) in R && a1 != a2) || (a1 == a2 && (b1,b2) in S)) :: ((a1,b1),(a2,b2))
}

lemma LexicographicLeftInOrder<T1(!new),T2(!new)>(p1: (T1,T2), p2: (T1,T2), R: BinaryRelation<T1,T1>, S: BinaryRelation<T2,T2>, A: iset<T1>, B: iset<T2>)
    requires RelationOn(R, A) && IsPartialOrder(R, A)
    requires RelationOn(S, B) && IsPartialOrder(S, B)
    requires p1.0 in A && p1.1 in B
    requires p2.0 in A && p2.1 in B
    requires (p1,p2) in LexicographicOrder(R, S, A, B)
    ensures (p1.0, p2.0) in R
{
    var a1, a2 := p1.0, p2.0;
    var b1, b2 := p1.1, p2.1;
    assert ((a1,a2) in R && a1 != a2) || (a1 == a2 && (b1,b2) in S) by {
        // by the definition of lexicographic order
        assert p1 == (a1,b1) && p2 == (a2,b2) && (p1,p2) in LexicographicOrder(R, S, A, B);
    }
    if a1 == a2
    {
        assert (a1,a2) in R by { assert Reflexive(R, A); } // since R is a partial order on A
    }
}

lemma LexicographicPartialOrder<T1(!new),T2(!new)>(R: BinaryRelation<T1,T1>, S: BinaryRelation<T2,T2>, A: iset<T1>, B: iset<T2>)
    requires PreR1: RelationOn(R, A)
    requires PreR2: IsPartialOrder(R, A)
    requires PreS1: RelationOn(S, B)
    requires PreS2: IsPartialOrder(S, B)
    ensures RelationOn(LexicographicOrder(R,S,A,B), CartesianProduct(A,B))
    ensures IsPartialOrder(LexicographicOrder(R,S,A,B), CartesianProduct(A,B))
// comment: the lexicographic order is actually even a total order


// Functions (as binary relations)

/*
הגדרה של פונקציה
(באופן שונה מהמוכר ומהמקובל בהסטוריה של מתמטיקה)
*/
type Function<!T1(!new,==),!T2(!new,==)> = F:  BinaryRelation<T1,T2> | ValidFunction(F) witness *

ghost predicate ValidFunction<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>)
{
    !exists x,y1,y2 :: (x,y1) in F && (x,y2) in F && y1 != y2 
}

lemma FunctionIsRelation<T1(!new),T2(!new)>(F: Function<T1,T2>) returns (R:  BinaryRelation<T1,T2>)
	ensures F == R
{
	R := F;
}

lemma NotEveryRelationIsFunction() returns (R:  BinaryRelation<int,int>)
	ensures !ValidFunction(R)
{
	R := iset{(1,2), (1,3)};
	assert !ValidFunction(R) by {
		var x, y1, y2 := 1, 2, 3;
		assert (x,y1) in R && (x,y2) in R && y1 != y2;
	}
}

/*
Alternative (equivalent) definition for functions
*/
ghost predicate ValidFunction'<T1(!new),T2(!new)>(F: iset<(T1,T2)>)
{
    forall p1,p2 :: p1 in F && p2 in F && p1.0 == p2.0 ==> p1.1 == p2.1
}

lemma EquivalentFunctionDefinitions<T1(!new),T2(!new)>(F: iset<(T1,T2)>)
	ensures ValidFunction(F) <==> ValidFunction'(F)
{
	calc {
		!ValidFunction'(F);
	== // by definition
		!forall p1,p2 :: p1 in F && p2 in F && p1.0 == p2.0 ==> p1.1 == p2.1;
	== // negation of quantifiers
		exists p1,p2 :: !(p1 in F && p2 in F && p1.0 == p2.0 ==> p1.1 == p2.1);
	== // rewriting negation of implication as a conjunction (with negation on the conseqent)
		exists p1,p2 :: p1 in F && p2 in F && p1.0 == p2.0 && p1.1 != p2.1;
	== // with (x,y1) for p1 and (x,y2) for p2, these claims are equivalent
		exists x,y1,y2 :: (x,y1) in F && (x,y2) in F && y1 != y2;
	== // double negation
		!(!exists x,y1,y2 :: (x,y1) in F && (x,y2) in F && y1 != y2);
	== // by definition
		!ValidFunction(F);
	}
}

ghost const F1:  BinaryRelation<real, real> := iset x, y | x*x + 3.0*x == y :: (x,y)

function Abs(n: int): int { if n >= 0 then n else -n } // if then else is like Java's ternary expressions n >= 0 ? n : -n

method M8Fa()
{
    assert ValidFunction(F1) by {
		assert !exists x,y1,y2 :: (x,y1) in F1 && (x,y2) in F1 && y1 != y2;
	 }
    // the square root on the integers for example is a relation, not a function
    var F1b:  BinaryRelation<int,int> := iset i:int,j:int | j*j == i :: (i,j);
    assert !ValidFunction(F1b) by { assert (9,-3) in F1b && (9,3) in F1b && -3 != 3; }

    var F1c:  BinaryRelation<int,int> := iset i:int,j:int | j*j == Abs(i) :: (i,j);
	 //assert ValidFunction(F1c);
}

// Definition: A function F is injective (חח"ע) if for any x1,x2 in Domain(F) with x1 != x2, we have F(x1) != F(x2)
ghost predicate InjectiveFunction<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>)
{
    ValidFunction(F) &&
    forall x1,x2,y1,y2 :: (x1,y1) in F && (x2,y2) in F && x1 != x2 ==> y1 != y2
}

/*
A given function is NOT injective if there are two ordered pairs
(x1,y) in F
(x2,y) in F
such that x1 != x2
*/
method M8Fb()
{
    var F2a := iset{(0,0), (1,2), (2,4)};
    assert ValidFunction(F2a);
    assert InjectiveFunction(F2a);
    assert Domain(F2a) == iset{0,1,2};
    assert Range(F2a) == iset{0,2,4};
    // in words: F2a is a function from the set {0,1,2} to the set {0,2,4}

    var F2b := F2a+iset{(3,4)};
    assert ValidFunction(F2b);
    assert !InjectiveFunction(F2b) by { assert (2,4) in F2b && (3,4) in F2b && 2!=3; }
    assert Domain(F2b) == Domain(F2a)+iset{3} == iset{0,1,2,3};
    assert Range(F2a) == Range(F2b) == iset{0,2,4};

    var F2c := F2b+iset{(3,2)};
    // F2c is a binary relation, but it is not a valid function
    assert !ValidFunction(F2c) by { assert (3,2) in F2c && (3,4) in F2c; }
}

/*

if F is a function from A to B,
for any superset B' of B we can say that F is a function from A to B' too;

if F : A -> B
and forall y in B there exists x in A s.t. F(x) = y (an in our binary-relation representation (x,y) in F)

we say that is a function onto B
פונקציה על
B

*/
ghost predicate SurjectiveFunction<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, A: iset<T1>, B: iset<T2>)
    requires ValidFunction(F) && A == Domain(F) && Range(F) <= B
{
    forall y :: y in B ==> exists x :: x in A && (x,y) in F
}


lemma FunctionOntoItsRange<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, A: iset<T1>, B: iset<T2>)
    requires ValidFunction(F) && A == Domain(F) && Range(F) <= B
    ensures SurjectiveFunction(F, A, B) <==> Range(F) == B
{}

ghost predicate SurjectiveFunction'<T1(!new),T2(!new)>(F: Function<T1,T2>, A: iset<T1>, B: iset<T2>)
    requires A == Domain(F) && Range(F) <= B
{
    Range(F) == B
}

lemma EquivalentSurjectiveDefinitions<T1(!new),T2(!new)>(F: Function<T1,T2>, A: iset<T1>, B: iset<T2>)
    requires A == Domain(F) && Range(F) <= B
    ensures SurjectiveFunction(F, A, B) <==> SurjectiveFunction'(F, A, B)
{}

ghost predicate BijectiveFunction<T1(!new),T2(!new)>(F: Function<T1,T2>, A: iset<T1>, B: iset<T2>)
    requires A == Domain(F) && Range(F) <= B
{
    InjectiveFunction(F) && SurjectiveFunction(F, A, B)
}

/* Advanced/Extra:

Functions and equivalence relations:

say F is a function, F : A -> B
we define on A a relation, E_F, such that for all a1,a2 in A

a1 E_F a2 if F(a1) = F(a2)
*/
ghost function RelationOnFunctionDomain<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, A: iset<T1>):  BinaryRelation<T1,T1>
    requires ValidFunction(F) && A == Domain(F)
{
    iset x1,x2,y | x1 in A && x2 in A && (x1,y) in F && (x2,y) in F :: (x1,x2)
}

/*

Claim: E_F is an equivalence relation on A

the equivalence class of a in A:

[a]_E_F = {x | x in A and F(x) = F(a) }

*/
lemma EquivalenceRelationOnFunctionDomain<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, A: iset<T1>)
    requires ValidFunction(F) && A == Domain(F)
    ensures EquivalenceRelation(RelationOnFunctionDomain(F, A), A)
{
    // Reflexive (a E_F a): F(a) = F(a)
    // Symmetric (a E_F b ==> b E_F a): F(a1) = F(a2) <==> F(a2) = F(a1)
    // Transitive (a E_F b and b E_F c ==> a E_F c): F(a) = F(b) /\ F(b) = F(c) ==> F(a) = F(c)
}

lemma {:verify false} EquivalenceRelationByFunctionToEquivalenceClasses<T(!new)>(E:  BinaryRelation<T,T>, A: iset<T>) returns (F:  BinaryRelation<T,iset<T>>)
    requires A == Domain(E) && RelationOn(E, A) && EquivalenceRelation(E, A)
    ensures ValidFunction(F) && A == Domain(F) && AllEquivalenceClasses(A, E) == Range(F) // Post1
    ensures RelationOnFunctionDomain(F, A) == E // Post2
{
    F := iset x | x in A :: (x,EquivalenceClassOf(x, A, E));
    // for Post1, this is the only property that Dafny did not immediately prove all by itself
    assert A <= Domain(F) by { assert forall x :: x in A ==> (x,EquivalenceClassOf(x, A, E)) in F; }
/*
say E is an equivalence relation on A,
define B = A/E the set of all equivalence classes; and define the function F : A -> B by F(a) = [a]_E

[well, more generally we could have said F : A -> Powerset(A); the function F is onto B; why?
since if Q in A/E is an equivalence class,
take q in Q, as Q is known to be a non-empty set, and we get F(q) = Q]

If we forget that B is the set of equivalence classes, we can recover the original E
from F_E: check for each pair of elements if F_E takes them both to the same element of B

*/
} 

/*
{(x,y) | (x,y) in F and x in A_0}

F |` A_0 : A_0 -> B

F |` A_0 <= F

*/
ghost function ReducedFunction<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, A0: iset<T1>):  BinaryRelation<T1,T2>
    requires ValidFunction(F)
{
    iset x,y | (x,y) in F && x in A0 :: (x,y)
}
// equivalently, we could define the reduction using set intersetion: F * (A0 X Range(F))

lemma ReducedFunctionIsSubset<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, A: iset<T1>)
    requires ValidFunction(F)
    ensures ReducedFunction(F, A) <= F
{}

lemma FunctionsIntersectionIsFunction<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, G:  BinaryRelation<T1,T2>)
    requires ValidFunction(F)
    requires ValidFunction(G)
    ensures ValidFunction(F*G)
{}

lemma FunctionsUnionIsNotAlwaysFunction() returns (F:  BinaryRelation<int,int>, G:  BinaryRelation<int,int>)
    ensures ValidFunction(F) && ValidFunction(G) && !ValidFunction(F+G)
{
    F, G := iset{(1,2)}, iset{(1,3)};
}

ghost predicate UnifiableFunctions<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, G:  BinaryRelation<T1,T2>)
    requires ValidFunction(F)
    requires ValidFunction(G)
{
    var A := Domain(F)*Domain(G);
    ReducedFunction(F, A) == ReducedFunction(G, A)
}

lemma FunctionUnionIsFunctionWhenDomainIntersectionAgrees<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, G:  BinaryRelation<T1,T2>)
    requires ValidFunction(F)
    requires ValidFunction(G)
    ensures ValidFunction(F+G) <==> UnifiableFunctions(F, G)

method M8Fc()
{
    var F3a, F3b := iset{(1,2),(2,3),(3,4),(4,5)}, iset{(3,4),(4,5),(5,6)};
    var F3c, F3d := F3a*F3b, F3a+F3b;
    assert F3c == iset{(3,4),(4,5)};
    assert ValidFunction(F3c) by { FunctionsIntersectionIsFunction(F3a, F3b); }
    assert F3d == iset{(1,2),(2,3),(3,4),(4,5),(5,6)};
    var A3 := Domain(F3a)*Domain(F3b);
    assert A3 == iset{3,4};
    assert 1: ReducedFunction(F3a, A3) == ReducedFunction(F3b, A3) == iset{(3,4),(4,5)};
    assert 2: UnifiableFunctions(F3a, F3b) by { reveal 1; }
    assert ValidFunction(F3d) by { reveal 2; FunctionUnionIsFunctionWhenDomainIntersectionAgrees(F3a, F3b); }
}

/*

Dafny's builtin type for functions: known as a lambda expression,
the => lets us construct anonymous functions
(even if in the following definition we end up giving it a name, by assigning it into a named constant)

*/

ghost const F1': real -> real := (x: real) => x*x + 3.0*x

ghost function Domain'<T1(!new),T2(!new)>(F: T1 -> T2): iset<T1> {
    iset x: T1 {:trigger true} | true // the function is defined for all elements of its argument's type
}

ghost function Range'<T1(!new),T2(!new)>(F: T1 -> T2): iset<T2> {
    iset x: T1 | true :: F(x)
}

/*

and Dafny's (known) syntax for the definition of named functions

*/

function F1''(x: real): real { x*x + 3.0*x }

method M8Fd()
{
    assert forall x, y :: (x,y) in F1 <==> y == F1'(x);
    assert forall x :: F1'(x) == F1''(x);
}

ghost predicate EquivalentFunctionDefinitions'<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, G: T1 -> T2)
    requires ValidFunction(F)
{
    forall x,y :: (x,y) in F <==> y == G(x)
}

ghost predicate InjectiveFunction'<T1(!new),T2(!new)>(F: T1 -> T2)
{
    forall x1,x2 :: x1 != x2 ==> F(x1) != F(x2)
}

lemma EquivalentInjectiveFunctionDefinitions<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, G: T1 -> T2)
    requires ValidFunction(F)
    requires EquivalentFunctionDefinitions'(F, G)
    ensures InjectiveFunction(F) <==> InjectiveFunction'(G)

ghost predicate SurjectiveFunction''<T1(!new),T2(!new)>(F: T1 -> T2, A: iset<T1>, B: iset<T2>)
    requires A == Domain'(F) && Range'(F) <= B
{
    forall y :: y in B ==> exists x :: x in A && y == F(x)
}

lemma EquivalentSurjectiveFunctionDefinitions<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>, G: T1 -> T2, A: iset<T1>, B: iset<T2>)
    requires ValidFunction(F) && A == Domain(F) == Domain'(G) && Range(F) <= B && Range'(G) <= B
    requires EquivalentFunctionDefinitions'(F, G)
    ensures SurjectiveFunction(F, A, B) <==> SurjectiveFunction''(G, A, B)
{}