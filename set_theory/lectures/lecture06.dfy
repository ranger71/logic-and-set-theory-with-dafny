/*
    Lecture 6: equivalence relations + equivalence classes (in preparation for "partitions" - next week)

    + definitions for reflexivity and symmetry (for binary relations with a single type in its domain and range)
*/
include "lecture05.dfy"

// reflexivity

ghost const AllIntegers := iset n: int | true
ghost const AllEvenNumbers := iset n: int | n%2 == 0
ghost const AllOddNumbers := iset n: int | n%2 != 0
ghost const AllOddNumbers' := iset n: int | n%2 == 1
ghost const AllOddNumbers'' := AllIntegers - AllEvenNumbers
ghost const AllOddNumbers''' := iset n: int | n !in AllEvenNumbers

// The relation R on the set A is reflexive if for any element "a" in A, the ordered pair (a,a) is in R
ghost predicate Reflexive<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires RelationOn(R, A)
{
    forall a :: a in A ==> (a,a) in R
}

// The set R on A is NOT reflexive if there is at least one element "a" in A
// such that the ordered pair (a,a) is NOT in R
ghost predicate NonReflexive<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires RelationOn(R, A)
{
    exists a :: a in A && (a,a) !in R
}

ghost const R6a := iset{(6,5)}
ghost const LessThan: BinaryRelation<int, int> := iset x, y | x < y :: (x, y)

method M6a()
{
	assert Reflexive(LessThanOrEqual_On_Integers, AllIntegers) by {
		assert (5,5) in LessThanOrEqual_On_Integers by { assert 5 <= 5; }
		// TODO: prove (exercise, using "forall" / "ensures")
	}
	assert !Reflexive(R6a, iset{5,6}) by {
		assert (6,5) in R6a; // irrelevant
		assert (5,6) !in R6a; // irrelevant
		assert (4,4) !in R6a; // irrelevant
		assert (5,5) !in R6a;
	}

	assert (0, 8) in LessThan;
	assert (-100, -99) in LessThan;
	assert (-100, -200) !in LessThan;
	assert !Reflexive(LessThan, AllIntegers) by {
		assert (-100, -100) !in LessThan;
	}
}

// The set R is symmetric if for any ordered pair (a,b) in R, the pair (b,a) is in R too
ghost predicate Symmetric<T(!new)>(R: BinaryRelation<T,T>) { forall a: T, b: T :: (a,b) in R <==> (b, a) in R }

// The set R is NOT symmetric if there exists at least one ordered pair (a,b) in R,
// such that the pair (b,a) is NOT in R
ghost predicate NonSymmetric<T(!new)>(R: BinaryRelation<T,T>) { exists a: T, b: T :: (a,b) in R && (b,a) !in R }

ghost const EqualIntegers: BinaryRelation<int, int> := iset x, y | x == y :: (x, y)
ghost const R6b := iset{(5,6)}
ghost const R6c := R6a+R6b

method M6b()
{
	assert !Symmetric(LessThanOrEqual_On_Integers) by {
		assert (5,6) in LessThanOrEqual_On_Integers by { assert 5 <= 6; }
		assert (6,5) !in LessThanOrEqual_On_Integers by { assert !(6 <= 5); }
	}
	assert !Symmetric(LessThan) by {
		assert (5,6) in LessThan by { assert 5 <= 6; }
		assert (6,5) !in LessThan by { assert !(6 <= 5); }
	}
	assert R6a == iset{(6,5)};
	assert R6b == iset{(5,6)};
	assert R6c == iset{(5,6), (6,5)};

	assert Symmetric(EqualIntegers);
	assert !Symmetric(R6a);
	assert !Symmetric(R6b);
	assert Symmetric(R6c);
}

// A transitive, reflexive, and symmetric relation R on the set A is called an equivalence relation
ghost predicate EquivalenceRelation<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires RelationOn(R, A)
{
    Transitive(R) && Reflexive(R, A) && Symmetric(R)
}

ghost const A61 := iset{0,1,2,3,4}
ghost const A62 := iset{0,1,2,4}
ghost const R61 := iset{(0,0),(0,2),(0,4),(1,1),(1,3),(2,0),(2,2),(2,4),(3,1),(3,3),(4,0),(4,2),(4,4)}
ghost const R62 := iset{(0,0),(0,2),(0,4),(1,1),(1,3),(2,0),(2,2),(2,4),(3,1),(4,0),(4,2),(4,4)}

method M6c()
{
    assert RelationOn(R61, A61);
    assert !RelationOn(R62, A62) by { assert (3,1) in R62 && 3 !in A62; }
    assert Reflexive(R61, A61);
    assert !Reflexive(R62, A61) by { assert 3 in A61 && (3,3) !in R62; }
    assert NonReflexive(R62, A61);
	 //assert Reflexive(R62, A62); // such a call is NOT allowed: Dafny correctly complans that "function precondition might not hold"!
}

ghost const R63 := iset{(0,0),(0,2),(1,1),(1,3),(2,0),(2,2),(2,4),(3,1),(4,0),(4,2),(4,4)}


method M6d()
{
    assert Symmetric(R61);
    assert NonSymmetric(R63) by { assert (4,0) in R63 && (0,4) !in R63; }
    assert !Symmetric(R63);
    assert EquivalenceRelation(R61, A61) by {
        assert RelationOn(R61, A61);
        assert Transitive(R61);
        assert Reflexive(R61, A61);
        assert Symmetric(R61);
    }
    assert !EquivalenceRelation(R62, A61) by {
        assert !Reflexive(R62, A61);
    }
}

// If R is an equivalence relation on the set A, we define for any element "a" of A its equivalence class (מחלקת שקילות)
// "a_R" to be a subset of A that includes each element "x" of A such that (a,x) is in R
ghost function EquivalenceClassOf<T>(a: T, A: iset<T>, R: BinaryRelation<T,T>): iset<T>
    requires a in A && RelationOn(R, A) && EquivalenceRelation(R, A)
{
    iset x | x in A && (a,x) in R
}

ghost const a0_R1 := EquivalenceClassOf(0, A61, R61)
ghost const a1_R1 := EquivalenceClassOf(1, A61, R61)
ghost const a2_R1 := EquivalenceClassOf(2, A61, R61)
ghost const a3_R1 := EquivalenceClassOf(3, A61, R61)
ghost const a4_R1 := EquivalenceClassOf(4, A61, R61)

method M6e()
{
    assert a0_R1 == a2_R1 == a4_R1  == iset{0,2,4};
    assert a1_R1 == a3_R1 == iset{1,3};
}

// Some properties of equivalence classes:

// a_R is always a subset of A
lemma EquivalenceClassesAreAlwaysSubsets<T>(a: T, A: iset<T>, R: BinaryRelation<T,T>)
    requires Pre1: a in A
    requires Pre2: RelationOn(R, A) && EquivalenceRelation(R, A)
    ensures EquivalenceClassOf(a, A, R) <= A
{
    // by the definition of EquivalenceClassOf, all elements are from the set A
    reveal Pre1,Pre2;
}

// "a" is a member of the set a_R (its own equivalence class)
lemma EquivalenceClassesAreAlwaysSelfInclusive<T>(a: T, A: iset<T>, R: BinaryRelation<T,T>)
    requires Pre1: a in A
    requires Pre2: RelationOn(R, A) && EquivalenceRelation(R, A)
    ensures a in EquivalenceClassOf(a, A, R)
{
    // by the definition of EquivalenceClassOf and by reflexivity of R on A, (a,a) in R
    reveal Pre1,Pre2;
}

// If b is in a_R then the ordered pairs (a,b) and (b,a) are in R
lemma PairsInEquivalenceClasses<T>(a: T, b: T, A: iset<T>, R: BinaryRelation<T,T>)
    requires Pre1: a in A
    requires Pre2: RelationOn(R, A) && EquivalenceRelation(R, A)
    requires Pre3: b in EquivalenceClassOf(a, A, R)
    ensures (a,b) in R
    ensures (b,a) in R
{
    // (a,b) in R from Pre3 and the definition of EquivalenceClassOf
    reveal Pre1,Pre2,Pre3;
    // (b,a) in R by the above and by symmetry
}
// (it is interesting to remove the symmetry conjunct from the definition of equivalence classes and see that Dafny correctly complains!)

// for any x1,x2 in a_R, the ordered pair (x1,x2) is in R
lemma PairsInEquivalenceClasses'<T>(a: T, x1: T, x2: T, A: iset<T>, R: BinaryRelation<T,T>)
    requires a in A
    requires RelationOn(R, A) && EquivalenceRelation(R, A)
    requires iset{x1, x2} <= EquivalenceClassOf(a, A, R)
    ensures (x1,x2) in R
{} // (x1,a) and (a,x2) are in R (by the previous lemma) and R is transitive

method M6f()
{
    var a,x1,x2 := 0,2,4;
    assert (2,4) in R61 by {
        assert iset{2,4} <= EquivalenceClassOf(0, A61, R61) == iset{0,2,4};
        PairsInEquivalenceClasses'(0, 2, 4, A61, R61);
    }
}

lemma EquivalenceClassesAreEitherEqualOrDisjoint<T>(a: T, b: T, A: iset<T>, R: BinaryRelation<T,T>)
    requires iset{a, b} <= A
    requires RelationOn(R, A) && EquivalenceRelation(R, A)
    ensures b in EquivalenceClassOf(a, A, R) ==> EquivalenceClassOf(a, A, R) == EquivalenceClassOf(b, A, R)
    ensures b !in EquivalenceClassOf(a, A, R) ==> EquivalenceClassOf(a, A, R) !! EquivalenceClassOf(b, A, R)
    // the !!, as in A !! B, is a convenient notation, in Dafny, for set disjointness (A*B=={})
    decreases b !in EquivalenceClassOf(a, A, R)
    // we will learn the significance of "decreases" later, when learning how to prove by induction in Dafny
{
    var a_R, b_R := EquivalenceClassOf(a, A, R), EquivalenceClassOf(b, A, R);
    if b in a_R
    {
        assert a_R == b_R by {
            assert a_R >= b_R by {
                forall x | x in b_R ensures x in a_R {
                    assert (b,x) in R; // lemma above
                    assert b in a_R; // guard
                    assert (a, b) in R; // assertion above + lemma above
                    assert (a, x) in R; // transitivity
                    assert x in a_R; // assertion above + lemma above? or definition of eq.cl.?
                }
            }
            assert a_R <= b_R by {
                forall x | x in a_R ensures x in b_R {
                    assert (b,x) in R; // again, from lemma above
                    assert x in b_R; // lemma above?
                }
            }
       }
    }
    else
    {
        assert b !in a_R; // negation of the guard
        assert a_R !! b_R by {
            forall t | t in a_R*b_R ensures false {
                var t_R := EquivalenceClassOf(t, A, R);
                assert t_R == a_R by { EquivalenceClassesAreEitherEqualOrDisjoint(t, a, A, R); } // by the first part above (and the choice of "t")
                assert t_R == b_R; // again by the first part above (and the choice of "t")
                assert a_R == b_R; // the two assertions above (and symmetry+transitivity of ==)
                assert b in a_R; // in contradiction to the negation of the guard, above
                assert false;
            }
        }
    }
}

// for each element of A there exists an equivalence class that contains it (its own)
lemma MembershipInEquivalenceClass<T>(a: T, A: iset<T>, R: BinaryRelation<T,T>) returns (b: T, b_R: iset<T>)
    requires a in A
    requires RelationOn(R, A) && EquivalenceRelation(R, A)
    ensures b in A && b_R == EquivalenceClassOf(b, A, R) && a in b_R
{
    b, b_R := a, EquivalenceClassOf(a, A, R);
}

// we denote the set of all equivalence classes of elements of A in the context of the relation R as A/R

// this is a set of non-empty subsets of A, each pair of distinct subsets is disjoint, and the union of all these sets is A
