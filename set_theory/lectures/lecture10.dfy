/*

Predicate Calculus / First-Order Logic

*/

// some earlier definitions + a few further definitions for relations and functions of other arities
module SetTheory_Definitions {
    type Relation<!T1(==),!T2(==)> = iset<(T1,T2)>
    ghost function Domain<T1(!new),T2(!new)>(R: Relation<T1,T2>): iset<T1>
    {
        iset x,y | (x,y) in R :: x
    }
    ghost function Range<T1(!new),T2(!new)>(R: Relation<T1,T2>): iset<T2>
    {
        iset x,y | (x,y) in R :: y
    }
    ghost predicate RelationOn<T(!new)>(R: Relation<T,T>, A: iset<T>) { forall a,b :: (a,b) in R ==> a in A && b in A }
    ghost predicate Reflexive<T(!new)>(R: Relation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        forall a :: a in A ==> (a,a) in R
    }
    ghost predicate Symmetric<T(!new)>(R: Relation<T,T>) { forall a,b :: (a,b) in R ==> (b,a) in R }
    ghost predicate Transitive<T(!new)>(R: Relation<T,T>) { forall a, b, c :: (a,b) in R && (b,c) in R ==> (a,c) in R }
    ghost predicate EquivalenceRelation<T(!new)>(R: Relation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
    	Transitive(R) && Reflexive(R, A) && Symmetric(R)
    }
    ghost predicate AntiSymmetric<T(!new)>(R: Relation<T,T>) { forall a,b :: (a,b) in R && (b,a) in R ==> a == b }
    type PartialOrder<!T(!new,==)> = R: iset<(T,T)> | IsPartialOrder(R, Domain(R)+Range(R))
    ghost predicate IsPartialOrder<T(!new)>(R: Relation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        Reflexive(R, A) && Transitive(R) && AntiSymmetric(R)
    }
    ghost predicate TotalOrder<T(!new)>(R: PartialOrder<T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        forall a,b :: a in A && b in A ==> (a,b) in R || (b,a) in R
    }
    ghost function CartesianProduct<T1,T2>(A: iset<T1>, B: iset<T2>): iset<(T1,T2)>
    {
        iset a,b | a in A && b in B :: (a,b)
    }
    ghost predicate MinimalElement<T(!new)>(y: T, A: iset<T>, R: PartialOrder<T>)
        requires y in A && RelationOn(R, A)
    {
        forall x :: x in A && (x,y) in R ==> x == y
    }
    ghost predicate Minimum<T(!new)>(y: T, A: iset<T>, R: PartialOrder<T>)
        requires y in A && RelationOn(R, A) && TotalOrder(R, A)
    {
        forall x :: x in A && (x,y) in R ==> x == y
    }
    type Relation1<!T(==)> = iset<T>
    type Relation3<!T1(==),!T2(==),!T3(==)> = iset<(T1,T2,T3)>
    type Function<!T1(!new,==),!T2(!new,==)> = F: Relation<T1,T2> | ValidFunction(F) witness *
    type Function2<!T1(!new,==),!T2(!new,==),!T3(!new,==)> = F: Relation3<T1,T2,T3> | ValidFunction2(F) witness *

    ghost function Domain2<T1(!new),T2(!new),T3(!new)>(F: Function2<T1,T2,T3>): iset<(T1,T2)>
    {
        iset triple | triple in F :: (triple.0,triple.1)
    }

    ghost function Range2<T1(!new),T2(!new),T3(!new)>(F: Function2<T1,T2,T3>): iset<T3>
    {
        iset triple | triple in F :: triple.2
    }

    ghost predicate ValidFunction<T1(!new),T2(!new)>(F: Relation<T1,T2>)
    {
        !exists x,y1,y2 :: (x,y1) in F && (x,y2) in F && y1 != y2 
    }

    ghost predicate ValidFunction2<T1(!new),T2(!new),T3(!new)>(F: Relation3<T1,T2,T3>)
    {
        !exists x,y,z1,z2 :: (x,y,z1) in F && (x,y,z2) in F && z1 != z2 
    }

    ghost predicate ValidFunctionDomain<T1(!new),T2(!new)>(F: Function<T1,T2>, A: iset<T1>)
    {
        A == Domain(F)
    }

    ghost predicate ValidFunction2Domain<T1(!new),T2(!new),T3(!new)>(F: Function2<T1,T2,T3>, A: iset<T1>, B: iset<T2>)
    {
        CartesianProduct(A,B) == Domain2(F)
    }
}

abstract module Language_0 {
    type T(!new)
}
abstract module AbstractStructure_0 refines Language_0 {
    ghost const U: iset<T> // the set of elements in our universe
}

module Structure_0a refines AbstractStructure_0 {
    type T(!new) = real
    ghost const U := iset{3.5}
}

module Structure_0b refines AbstractStructure_0 {
    type T(!new) = int
    ghost const U := iset{-1, 0, 1}
}

abstract module Sentence_0 {
    import opened Structure_Of_Language_0 : AbstractStructure_0

    ghost predicate AtLeastTwoElements() { exists x, y :: x in U && y in U && x != y }

    // claim: there are at least two distinct elements in our structure's universe
    lemma Sentence()
        ensures AtLeastTwoElements()
}

abstract module ClaimDoesNotHold_0a refines Sentence_0 {
    import opened Structure_Of_Language_0 = Structure_0a // choosing a concrete structure

    lemma {:verify false} Sentence() // cannot prove, as the claim does NOT hold on this structure
        ensures AtLeastTwoElements()
    {
        assert forall x :: x in U ==> x == 3.5; // there are NO two distinct ellements in this structure's universe
    }
}

// this time the module is not abstract: it is concrete, it includes a proof -
// like a class implementing an interface in object-oriented programming
module ClaimHolds_0b refines Sentence_0 {
    import opened Structure_Of_Language_0 = Structure_0b // choosing the other concrete structure this time

    lemma Sentence()
        ensures AtLeastTwoElements()
    {
        assert 0 in U && 1 in U && 0 != 1;
    }
}

abstract module Language_1 {
    import opened SetTheory_Definitions
    type T(!new)

    ghost const P: Relation1<T>
    ghost const R: Relation3<T,T,T>
    ghost const F: Function<T,T>
    ghost const G: Function2<T,T,T>
}

abstract module AbstractStructure_1 refines Language_1 {
    ghost const U: iset<T>
}

/*
U^M={1,2,3,4,5}
P^M={2,4,5}
F^M={<1,2>,<2,2>,<3,1>,<4,5>,<5,1>}
G^M={(<x,y>,z)|z=max{x,y}}
R^M={(3,4,1),(1,2,3),(4,4,2)}
*/
module Structure_1M refines AbstractStructure_1 {
    newtype T = n: int | 1 <= n <= 5 witness 4
    ghost const U: iset<T> := iset n: T | true

    ghost const P := iset{2,4,5}
    ghost const R := iset{(3,4,1), (1,2,3), (4,4,2), (3,4,4)}
    ghost const F := iset{(1,2), (2,2), (3,1), (4,5), (5,1)}
    ghost const G := iset x,y,z | z == max(x as int,y as int) as T :: (x,y,z)
/* Equivalently, we could have defined the relations and functions this way (enabling function calls with a simpler syntax):
    ghost predicate P(n: T) requires n in U { n == 2 || n == 4 || n == 5 }
    ghost predicate R(x: T, y: T, z: T) requires x in U && y in U && z in U
    {
        (x,y,z) == (3,4,1) || (x,y,z) == (1,2,3) || (x,y,z) == (4,4,2) ||
        (x,y,z) == (3,4,4)
    }
    ghost function F(i: T): T requires i in U
    {
        match i
        case 1 => 2 as T
        case 2 => 2 as T
        case 3 => 1 as T
        case 4 => 5 as T
        case 5 => 1 as T
    }
    ghost function G(m: T, n: T): T requires m in U && n in U { max(m as int ,n as int) as T }
*/
    ghost function max(x: int, y: int): int { if x >= y then x else y }
}

/*
One more structure N

U^N=N={0,1,2,...}
P^N=even numbers
R^N={(x,y,x)|x+y<z}
F^N:N-->N
F^N(i) = i+1
G^N:N X N --> N
G^N(m,n) = m*n
*/
module Structure_1N refines AbstractStructure_1 {
    newtype T = n: int | 0 <= n witness 19 // all natural numbers
    ghost const U: iset<T> := iset n: T | true

    ghost const P := iset x | x in U && x%2 == 0
    ghost const R := iset x,y,z | x in U && y in U && z in U && x+y < z :: (x,y,z)
    ghost const F := iset i,res | i in U && res == i+1 :: (i,res)
    ghost const G := iset m,n,res | m in U && n in U && res == m*n :: (m,n,res)
/* and again here's an alternative definition:
    ghost predicate P(n: T) requires n in U { n%2 == 0 }
    ghost predicate R(x: T, y: T, z: T) requires x in U && y in U && z in U
    {
        x+y < z
    }
    ghost function F(i: T): T requires i in U { i+1 }
    ghost function G(m: T, n: T): T requires m in U && n in U { m*n }
*/
}

abstract module SAT_1 {
    import opened Structure_Of_Language_1 : AbstractStructure_1
    import opened SetTheory_Definitions

    lemma Sat() returns (x: T, y: T)
        requires ValidFunction2(G) && ValidFunction2Domain(G, U, U)
        ensures (x,y) in Domain2(G)
        // a formula with two free variiables: x,y
        ensures exists Gxy :: (x, y, Gxy) in G
        ensures forall Gxy :: (x, y, Gxy) in G ==> (x, y, Gxy) in R
        //ensures R(x, y, G(x,y)) // the alternative definition would be eaier to use, as it supports direct calling to the functions and the predicates
}

module SAT_1M refines SAT_1 {
    import opened Structure_Of_Language_1 = Structure_1M // choosing a concrete structure

    lemma {:verify true} Sat() returns (x: T, y: T)
        // the previously declared formula with two free variiables: is it satisfiable?
    {
        x, y := 3, 4; // the formula is satisfiable, and here's a satisfying assignment
        assert ValidFunction2(G) && ValidFunction2Domain(G, U, U) && 3 in U && 4 in U;
        assert (3,4,4) in G;
        assert (3,4,4) in R;
    }
}

// on this simple language with one predicate "P", let's demonstrate logical implication that holds for ANY structure of that language
abstract module Language_2 {
    import opened SetTheory_Definitions
    type T(!new)

    ghost const P: Relation<T,T>
}
abstract module AbstractStructure_2 refines Language_2 {
    ghost const U: iset<T>

    // for all structure M with a binary relation P and a non-empty universe U,
    // if   "M |= exists y :: y in U /\ (forall x :: x in U --> (x,y) in P)"
    // then "M |= forall x :: x in U /\ (exists y :: y in U /\ (x,y) in P)"
    lemma ExistsForallImpliesForallExists<T>()
        requires U != iset{} // this requirement was not really required here,
        // still, we state it since by definition, any structure is defined on a non-empty universe
        ensures (exists y :: y in U && (forall x :: x in U ==> (x,y) in P))
            ==> (forall x :: x in U ==> (exists y :: y in U && (x,y) in P))
    {
        // Dafny accpets this, still here's a possible proof for the human reader
        if exists y :: y in U && (forall x :: x in U ==> (x,y) in P)
        {
            var y :| y in U && (forall x :: x in U ==> (x,y) in P);
            assert forall x :: x in U ==> (x,y) in P;
        }
    }

    // and in predicate calculus it is common use "==>" for such general implications
    // (in contrast to the --> in a regular formula; yet in Dafny we use ==> in both case) -
    // these are implications (sometimes referred to as "entailement")
    // for all structures of the language / for any interpretation of the relation P on any non-empty universe U

    // interestingly, the revese implication does not hold

    // it is NOT the case that for all structure M with a binary relation P and a non-empty universe U,
    // if   "M |= forall x :: x in U /\ (exists y :: y in U /\ (x,y) in P)"
    // then "M |= exists y :: y in U /\ (forall x :: x in U --> (x,y) in P)"
    lemma {:verify false} ForallExistsDoesNotImplyExistsForall<T>()
        ensures !forall P: Relation<T,T>, U: iset<T>{:trigger trig2(P,U)} ::
            (exists y :: y in U && (forall x :: x in U ==> (x,y) in P))
            <== (forall x :: x in U ==> (exists y :: y in U && (x,y) in P))

    ghost predicate trig2<T1,T2>(x: T1, y: T2) { true }
}

abstract module Language_Naturals {
    type T

    const Zero: T
    const One: T

    ghost predicate LessThan(m: T, n: T)
    ghost function Plus(x: T, y: T): T
    ghost function Times(x: T, y: T): T
}

abstract module AbstractStructure_Naturals refines Language_Naturals {
    ghost const U: iset<T>
}

module Structure_Naturals refines AbstractStructure_Naturals {
    newtype T = n: int | 0 <= n witness 19 // all natural numbers
    ghost const U: iset<T> := iset n: T | true

    const Zero: T := 0
    const One: T := 1

    ghost predicate LessThan(m: T, n: T) { m < n }
    ghost function Plus(x: T, y: T): T { x + y }
    ghost function Times(x: T, y: T): T { x * y }
}

// N |= forall x forall y (x+y=y+x)
module M1
{
    import opened Structure_Naturals
    // recall that in Dafny sending parameters to a lemma is a convenient way to express universal quantification (forall);
    // and as we quantify (in predicate calculus) over elements from the structure's universe, we conveniently state this
    // in Dafny as preconditions to the lemma (the "requires")
    lemma L1(x: T, y: T)
        requires x in U && y in U
        ensures Plus(x,y) == Plus(y,x)
    {
        assert Plus(x,y) == x+y == y+x == Plus(y,x);
    }
}

/*
N |=? forall x (1+(1+1)) < x

unsatisfiable

*/
module M2 {
    import opened Structure_Naturals
    lemma {:verify false} UNSAT_1(x: T)
        requires x in U
        ensures LessThan(Plus(One,Plus(One,One)), x)
    {
        // and indeed, the lemma cannot be proved!
        // the formula in the "ensures" clause by itself has many satisfying assignments;
        // but the lemma expresses a more general claim, that this formula should hold for ALL x in U,
        // and this does not hold, for example:
        assert !LessThan(Plus(One,Plus(One,One)), One);
    }
}

/*
N |=? (1+(1+1)) < x
N not |= (1+(1+1)) < x [3]
*/
module M3
{
    import opened Structure_Naturals
    lemma UNSAT_1() returns (x: T)
        ensures x in U
        // a formula with one free variable
        ensures LessThan(Plus(One,Plus(One,One)), x)
    {
        x := 5; // one of many possible satisfying assignments
        assert LessThan(Plus(One,Plus(One,One)), x) <==> Plus(One,Plus(One,One)) < x;
        assert Plus(One,Plus(One,One)) < x by {
            calc {
                Plus(One,Plus(One,One));
            ==
                Plus(1,Plus(1,1));
            ==
                Plus(1,1+1);
            ==
                Plus(1,2);
            ==
                1+2;
            ==
                3;
            <
                5;
            ==
                x;
            }
        }
    }
}

// N |=? exists x (1+(1+1)) < x
module M4 {
    import opened Structure_Naturals
    import M3
    lemma UNSAT_1()
        // a formula with no free variables: a (first-order) sentence / פסוק
        ensures exists x :: x in U && LessThan(Plus(One,Plus(One,One)), x)
    {
        // this time, with no free variables we are not expected to produce a satisying assignment,
        // just say if the formula is true or false; when priving it is true, we can decomopose it,
        // and show the existance of a satisfying assignent to the subexpression inside the existential quantifier,
        // which makes that quantifier (and the full sentence) true
        var x := M3.UNSAT_1();
        assert x in U && LessThan(Plus(One,Plus(One,One)), x);
        assert exists x :: x in U && LessThan(Plus(One,Plus(One,One)), x);
    }
}

/*
forall x ( forall y (P(y) \/ Q(x,y) --> forall x (R(x,y))
*/
ghost predicate FormulaUsingThreePredicatesThreeBoundBooleanVariablesAndOnlyOneFreeBoolean(P: real -> bool, Q: (int, real) -> bool, R: (nat, nat) -> bool, y: nat)
{
    // only the rightmost "y" is free in this formula (along with P,Q,R of course)
    forall x: int{:trigger trig1(x)} :: (forall y: real :: P(y) || Q(x,y)) ==> forall x: nat :: R(x,y)
}

ghost predicate trig1<T>(n: T) { true }

module M5 {
    import opened Structure_Naturals
    lemma SatisfyingAssignment() returns (x1: T, x2: T)
        ensures x1 in U && x2 in U && LessThan(x1,x2)
    {
        x1, x2 := 3, 5; // this is a simple example of a satisfying assignment:
        // it assigns valid values to the free variables in the formula "LessThan(x1,x2)"
        // and substituting these values for the variables makes the formula "hold"
        // meaning its value is "true";
        // this goes as evidence that the formula is satisfiable by the structure of narural numbers;
        // whereas on a different structure it might still be unsatisfiable
        calc {
            x1;
        ==
            3;
        <
            5;
        ==
            x2;
        }
        assert LessThan(3, 5);
    }
}

// N not |= x1 < x2 [3,3]
module M6 {
    import opened Structure_Naturals
    lemma {:verify false} NonSatisfyingAssignment() returns (x1: T, x2: T)
        ensures x1 in U && x2 in U
        ensures LessThan(x1,x2)
    {
        x1, x2 := 3, 3; // this is a simple example of a NON-satisfying assignment:
        // it assigns values to the free variables in the formula "LessThan(x1,x2)"
        // yet substituting these values for the variables DOES NOT makes the formula "hold";
        // its value is "false";
        // whenever all assignments are non-satisfying, the sentence is unsatisfiable;
        // it is a false sentece; but not in this case here (as we could see above)
        assert !LessThan(3,3);
    }
}