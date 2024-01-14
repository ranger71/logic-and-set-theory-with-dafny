module SetTheory_Definitions {
    // from lecture02.dfy
    ghost function SetUnion<T(!new)>(A: iset<T>, B: iset<T>): iset<T>
    {
        iset x: T | x in A || x in B
    }

    ghost function SetIntersection(A: set, B: set): set
    {
        set x | x in A && x in B
    }

    ghost function SetDifference(A: set, B: set): set
    {
        set y | y in A && y !in B
    }

    // from lecture03.dfy
    ghost predicate IsSubset(A: set, B: set) // <=
    {
        forall n :: n in A ==> n in B // same as the next line
        //forall n :: if n in A then n in B else true // same as "A <= B"
    }

    ghost predicate IsStrictSubset(A: set, B: set) // "<"
    {
        IsSubset(A, B) &&
        (exists m :: m in B && m !in A)
    }

    ghost predicate DisjointSets(A: set, B: set) { SetIntersection(A, B) == {} }

    lemma SubsetsInDafny(A: set, B: set)
        ensures A<=B <==> IsSubset(A, B)
        ensures A>=B <==> IsSubset(B, A) // we can also say that A is a superset of B
    {}

    ghost predicate IsSuperset(A: iset, B: iset)
    {
        forall n :: n in B ==> n in A // same as "A >= B"
    }

    // from lecture04.dfy

    lemma ModusPonens(P: bool, Q: bool)
        requires P ==> Q
        requires P
        ensures Q
    {}

    // one other way of writing this: 
    lemma ModusPonens'(P: bool, Q: bool)
        ensures ((P ==> Q) && P) ==> Q
    {}

    lemma ExtensionalityAxiom(A: set, B: set)
        ensures (A==B) <==> (forall x :: x in A <==> x in B)
    {}// well, it's an axiom, so no need to prove it;
    // yet the empty proof shows that Dafny knows about it and accepts it

    lemma FromExtensionalityInNegation(A: set, B: set)
        ensures (A==B) <==> (forall x :: x !in A <==> x !in B)
    {}

    lemma BidirectionImplication(P: bool, Q: bool)
        ensures (P <==> Q) == ((P ==> Q) && (P <== Q))
    {}

    lemma BidirectionImplicationWithNegation(P: bool, Q: bool)
        ensures (P <==> Q) == ((P ==> Q) && (!P ==> !Q))
    {
        calc {
            (P <==> Q);
        == { BidirectionImplication(P,Q); }
            ((P ==> Q) && (P <== Q));
        == // definition of implication using negtion and disjunction
            ((P ==> Q) && (P || !Q));
        == // double negation
            ((P ==> Q) && (!!P || !Q));
        ==
            ((P ==> Q) && (!P ==> !Q));
        }
    }

    lemma {:verify true} ExtensionalityUsingSetInclusion(A: set, B: set)
        requires 1: A <= B
        requires 2: B <= A
        ensures A == B
    {
        assert 3: forall x :: x in A <==> x in B by {
            forall x ensures x in A <==> x in B {
                if x in A
                {
                    assert x in B by { reveal 1; } // by defintion of the set inclusion relation
                    assert x in A && x in B;
                }
                else if x in B // leading to contradiction
                {
                    assert 4: x !in A; // from the first guard
                    assert 5: x in B; // from the second guard
                    assert 6: x in A by { reveal 2,5; }
                    assert false by {reveal 4,6; }
                }
                else {
                    assert x !in A && x !in B;
                }
            }
        }
        assert A == B by { reveal 3; ExtensionalityAxiom(A, B); }
    }

    // from lecture05.dfy
    lemma EqualityOfOrderedPairs<T1, T2>(p1: (T1, T2), p2: (T1, T2))
        ensures p1 == p2 <==> p1.0 == p2.0 && p1.1 == p2.1
    {}

    type BinaryRelation<!T1(==),!T2(==)> = iset<(T1, T2)>

    ghost predicate RelationOn<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>) {
        forall a,b :: (a,b) in R ==> a in A && b in A // forall p :: p in R ==> p.0 in A && p.1 in A
    }

    ghost predicate Transitive<T(!new)>(R: BinaryRelation<T,T>) { forall a, b, c :: (a,b) in R && (b,c) in R ==> (a,c) in R }
    ghost predicate NonTransitive<T(!new)>(R: BinaryRelation<T,T>) { exists a, b, c :: (a,b) in R && (b,c) in R && (a,c) !in R }

    // from lecture06.dfy

    ghost predicate Reflexive<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        forall a :: a in A ==> (a,a) in R
    }

    ghost predicate NonReflexive<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        exists a :: a in A && (a,a) !in R
    }

    ghost predicate Symmetric<T(!new)>(R: BinaryRelation<T,T>) { forall a: T, b: T :: (a,b) in R <==> (b, a) in R }

    ghost predicate NonSymmetric<T(!new)>(R: BinaryRelation<T,T>) { exists a: T, b: T :: (a,b) in R && (b,a) !in R }

    ghost predicate EquivalenceRelation<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        Transitive(R) && Reflexive(R, A) && Symmetric(R)
    }

    ghost function EquivalenceClassOf<T>(a: T, A: iset<T>, R: BinaryRelation<T,T>): iset<T>
        requires a in A && RelationOn(R, A) && EquivalenceRelation(R, A)
    {
        iset x | x in A && (a,x) in R
    }

    // from lecture07.dfy

    ghost function UnaryUnion<T>(As: iset<iset<T>>): iset<T> {
        iset a,A | A in As && a in A :: a
    }

    ghost predicate PairwiseDisjoint<T>(As: iset<iset<T>>) {
        forall A,B :: A in As && B in As && A != B ==> A !! B // "A !! B" is short for "disjoint": A*B == iset{}
    }

    ghost predicate NonEmptyISets<T>(As: iset<iset<T>>) {
        forall A :: A in As ==> A != iset{}
    }

    ghost predicate IsPartition<T>(P: iset<iset<T>>, A: iset<T>) {
        NonEmptyISets(P) && PairwiseDisjoint(P) && UnaryUnion(P) == A
    }

    ghost function AllEquivalenceClasses<T>(A: iset<T>, R: BinaryRelation<T,T>): iset<iset<T>>
        requires RelationOn(R, A) && EquivalenceRelation(R, A)
    {
        iset a | a in A :: EquivalenceClassOf(a, A, R)    
    }

    ghost predicate AntiSymmetric<T(!new)>(R: BinaryRelation<T,T>) { forall a: T, b: T :: (a,b) in R && (b,a) in R ==> a == b }

    ghost predicate IsPartialOrder<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        Transitive(R) && Reflexive(R, A) && AntiSymmetric(R)
    }

    ghost function Domain<T1(!new),T2(!new)>(R: BinaryRelation<T1,T2>): iset<T1> { iset pair | pair in R :: pair.0 } // תחום
    ghost function Range<T1(!new),T2(!new)>(R: BinaryRelation<T1,T2>): iset<T2> { iset pair | pair in R :: pair.1 } // טווח/תמונה
    ghost function isetOf<T(!new)>(R: BinaryRelation<T,T>): iset<T> { Range(R) + Domain(R) }

    type PartialOrder<!T(!new,==)> = R: BinaryRelation<T,T> | var A := isetOf(R); RelationOn(R, A)&& IsPartialOrder(R, A)

    ghost function Powerset<T>(A: iset<T>): iset<iset<T>> {
        iset B | B <= A
    }

    ghost function CartesianProduct<T1,T2>(A: iset<T1>, B: iset<T2>): iset<(T1,T2)> {
        iset a,b | a in A && b in B :: (a,b)
    }

    lemma BinaryRelationIsSubsetOfCartesianProduct<T1,T2>(R: BinaryRelation<T1, T2>, A: iset<T1>, B: iset<T2>)
        requires A == Domain(R)
        requires B == Range(R)
        ensures R <= CartesianProduct(A, B)
    {}

    ghost function SubsetRelation(A: iset): BinaryRelation<iset, iset> {
        iset subset1,subset2 | subset1 <= subset2 <= A :: (subset1,subset2)
    }

    // from lecture08.dfy

    ghost predicate IsTotalOrder<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
        requires RelationOn(R, A)
    {
        IsPartialOrder(R, A) && forall a,b :: a in A && b in A ==> (a,b) in R || (b,a) in R
    }

    // Here's an alternative definition:
    ghost predicate IsTotalOrder'<T(!new)>(R: PartialOrder<T>, A: set<T>) {
        forall a,b :: a in A && b in A ==> (a,b) in R || (b,a) in R
    }

    ghost function InverseRelation<T1(!new),T2(!new)>(R: BinaryRelation<T1,T2>): BinaryRelation<T2,T1> {
        iset x,y | x in Domain(R) && y in Range(R) && (x,y) in R :: (y,x)
    }

    ghost function IdentityRelation<T>(A: iset<T>): BinaryRelation<T,T> {
        iset a | a in A :: (a, a)
    }

    // Functions (as binary relations)

    type Function<!T1(!new,==),!T2(!new,==)> = F:  BinaryRelation<T1,T2> | ValidFunction(F) witness *

    ghost predicate ValidFunction<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>) {
        !exists x,y1,y2 :: (x,y1) in F && (x,y2) in F && y1 != y2 
    }

    // Alternative (equivalent) definition for functions
    ghost predicate ValidFunction'<T1(!new),T2(!new)>(F: iset<(T1,T2)>) {
        forall p1,p2 :: p1 in F && p2 in F && p1.0 == p2.0 ==> p1.1 == p2.1
    }

    ghost predicate ValidFunctionDomain<T1(!new),T2(!new)>(F: Function<T1,T2>, A: iset<T1>) {
        A == Domain(F)
    }

    ghost predicate InjectiveFunction<T1(!new),T2(!new)>(F:  BinaryRelation<T1,T2>) {
        ValidFunction(F) &&
        forall x1,x2,y1,y2 :: (x1,y1) in F && (x2,y2) in F && x1 != x2 ==> y1 != y2
    }

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

    // A~B if there exists an injective+surjective (i.e. bijective) F:A->B
    ghost predicate CardinallyEquivalentSets<T1(!new),T2(!new)>(A: iset<T1>, B: iset<T2>)
    {
        exists F: Function<T1, T2> :: ValidFunctionDomain(F, A) && Range(F) <= B && BijectiveFunction(F, A, B)
    }
}