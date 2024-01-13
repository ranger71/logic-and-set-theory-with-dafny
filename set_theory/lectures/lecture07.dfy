/*
    Lecture 7: partition + partial order relations (and total order, next week)

    Also:
    - anti-symmetry
    - cartesian products
    - powersets
    - assume statements
    - definition of a new type in Dafny with a type invariant
*/
include "lecture06.dfy"

// we denote the set of all equivalence classes of elements of A in the context of the relation R as A/R

// this is a set of non-empty subsets of A, each pair of distinct subsets is disjoint, and the union of all these sets is A
// we denote the set of all equivalence classes of elements of A in the context of the relation R as A/R

// this is a set of non-empty subsets of A, each pair of distinct subsets is disjoint, and the union of all these sets is A

// We define a partition of a set to be any set of pairwise-disjoint non-empty subsets whose union is the original set
ghost function UnaryUnion<T>(As: iset<iset<T>>): iset<T>
{
    iset a,A | A in As && a in A :: a
}

ghost predicate PairwiseDisjoint<T>(As: iset<iset<T>>)
{
    forall A,B :: A in As && B in As && A != B ==> A !! B // "A !! B" is short for "disjoint": A*B == iset{}
}

ghost predicate NonEmptyISets<T>(As: iset<iset<T>>)
{
    forall A :: A in As ==> A != iset{}
}

ghost predicate IsPartition<T>(P: iset<iset<T>>, A: iset<T>)
{
    NonEmptyISets(P) && PairwiseDisjoint(P) && UnaryUnion(P) == A
}

method M7a()
{
	assert AllEvenNumbers == iset x | x%2 == 0;
	assert AllOddNumbers == iset x | x%2 == 1;
	assert AllIntegers == iset n: int | true;
	ghost var EvenAndOddNumbers: iset<iset<int>> := iset{AllEvenNumbers, AllOddNumbers};
	assert IsPartition(EvenAndOddNumbers, AllIntegers) by {
		var P, A := EvenAndOddNumbers, AllIntegers;
		assert NonEmptyISets(P) by {
			var As := P;
			assert forall A :: A in As ==> A != iset{} by {
				forall A | A in As ensures A != iset{} {
					assert A in As;
					calc {
						A in As;
					==
						A in P;
					==
						A in EvenAndOddNumbers;
					==
						A in iset{AllEvenNumbers, AllOddNumbers};
					==
						A == AllEvenNumbers || A == AllOddNumbers;
					== {
							assert AllEvenNumbers != iset{} && AllOddNumbers != iset{} by {
								assert 2 in AllEvenNumbers;
								assert 3 in AllOddNumbers;
							} }
						A != iset{};
					}
				}
				assert A != iset{};
			}
		}
		assert PairwiseDisjoint(P);
		assert UnaryUnion(P) == A by {
			assert (iset a,A' | A' in EvenAndOddNumbers && a in A' :: a) == AllIntegers by {
				forall x ensures x in (iset a,A' | A' in EvenAndOddNumbers && a in A' :: a) <==> x in AllIntegers {
					assert x in AllEvenNumbers || x in AllOddNumbers;
				}
			}
		}
	}
}

// Whenever R is an equivalence relation on the set A, its equivalence classes form a partition

ghost function AllEquivalenceClasses<T>(A: iset<T>, R: BinaryRelation<T,T>): iset<iset<T>>
    requires RelationOn(R, A) && EquivalenceRelation(R, A)
{
    iset a | a in A :: EquivalenceClassOf(a, A, R)    
}

lemma DisjointPairsOfEquivalenceClasses<T>(a_R: iset<T>, b_R: iset<T>, A: iset<T>, R: BinaryRelation<T,T>)
    requires RelationOn(R, A) && EquivalenceRelation(R, A)
    requires a_R in AllEquivalenceClasses(A, R)
    requires b_R in AllEquivalenceClasses(A, R)
    ensures a_R == b_R || a_R !! b_R
{}

lemma AllEquivalenceClasses_Form_A_Partition<T>(A: iset<T>, R: BinaryRelation<T,T>)
    requires RelationOn(R, A) && EquivalenceRelation(R, A)
    ensures IsPartition(AllEquivalenceClasses(A, R), A)
// Proof left as an exercise

method {:verify true} M7b()
{
    var P := AllEquivalenceClasses(A61, R61);
    assert P == iset{a0_R1, a1_R1} by { // repeating from M2 above:
        assert a0_R1 == a2_R1 == a4_R1  == iset{0,2,4};
        assert a1_R1 == a3_R1 == iset{1,3};
    }
    assert IsPartition(P, A61) by { AllEquivalenceClasses_Form_A_Partition(A61, R61); }
}

// representing a partial order on a set using binary relations:

// a binary relation R is anti-symmetric if there are no a,b such that a!=b and both pairs (a,b) and (b,a) are in R;
// the common way to define this property is as follows:
ghost predicate AntiSymmetric<T(!new)>(R: BinaryRelation<T,T>) { forall a: T, b: T :: (a,b) in R && (b,a) in R ==> a == b }

// a transitive, reflexive, and anti-symmetric relation R on the set A forms a partial order on the elements of A
ghost predicate IsPartialOrder<T(!new)>(R: BinaryRelation<T,T>, A: iset<T>)
    requires RelationOn(R, A)
{
    Transitive(R) && Reflexive(R, A) && AntiSymmetric(R)
}

ghost function Domain<T1(!new),T2(!new)>(R: BinaryRelation<T1,T2>): iset<T1> { iset pair | pair in R :: pair.0 } // תחום
ghost function Range<T1(!new),T2(!new)>(R: BinaryRelation<T1,T2>): iset<T2> { iset pair | pair in R :: pair.1 } // טווח/תמונה
ghost function isetOf<T(!new)>(R: BinaryRelation<T,T>): iset<T> { Range(R) + Domain(R) }

const R7a: iset<(int,int)> := iset{(5,5), (5,6), (5,7), (6,6), (6,9)}

type PartialOrder<!T(!new,==)> = R: BinaryRelation<T,T> | var A := isetOf(R); RelationOn(R, A)&& IsPartialOrder(R, A)

// the set inclusion relation is a partial order

ghost const A7b := iset{1,2,3}
ghost const PowersetOfA7b := iset{iset{}, iset{1}, iset{2}, iset{3}, iset{1,2}, iset{1,3}, iset{2,3}, iset{1,2,3}}

// the set of all subsets is known as the powerset of a given set
ghost function Powerset<T>(A: iset<T>): iset<iset<T>>
{
	iset B | B <= A
}

ghost function CartesianProduct<T1,T2>(A: iset<T1>, B: iset<T2>): iset<(T1,T2)>
{
    iset a,b | a in A && b in B :: (a,b)
}

lemma BinaryRelationIsSubsetOfCartesianProduct<T1,T2>(R: BinaryRelation<T1, T2>, A: iset<T1>, B: iset<T2>)
	requires A == Domain(R)
	requires B == Range(R)
	ensures R <= CartesianProduct(A, B)
{}

method M7c()
{
	assume Powerset(A7b) == PowersetOfA7b; // prove? exercise
	ghost var subsetRelationOnA7b := SubsetRelation(A7b); 
	assume Domain(subsetRelationOnA7b) ==  Powerset(A7b);
	assume Range(subsetRelationOnA7b) ==  Powerset(A7b);
	assert subsetRelationOnA7b <= CartesianProduct(PowersetOfA7b, PowersetOfA7b) by {
		BinaryRelationIsSubsetOfCartesianProduct(subsetRelationOnA7b, PowersetOfA7b, PowersetOfA7b);
	}
}

ghost function SubsetRelation(A: iset): BinaryRelation<iset, iset>
{
    iset subset1,subset2 | subset1 <= subset2 <= A :: (subset1,subset2)
}

// proof added after the lecture
lemma SetInclusionIsPartialOrderOnPowerset<T(!new)>(A: iset<T>, R: BinaryRelation<iset<T>, iset<T>>)
    requires R == SubsetRelation(A)
    ensures IsPartialOrder(R, Powerset(A))
{
    var P := Powerset(A);
    assert RelationOn(R, P);
    assert Reflexive(R, P) by {
//        forall s | s <= A ensures (s,s) in R {
        forall s | s in P ensures (s,s) in R {
				assert s <= A;
            assert s <= s <= A;
        }
    }
    assert Transitive(R) by {
        forall s1,s2,s3 | (s1,s2) in R && (s2,s3) in R ensures (s1,s3) in R {
            assert s1 <= s2 <= A;
            assert s2 <= s3 <= A;
            assert s1 <= s3 <= A;
        }
    }
    assert AntiSymmetric(R) by {
        forall s1,s2 | (s1,s2) in R && (s2,s1) in R ensures s1 == s2 {
            assert s1 <= s2;
            assert s2 <= s1;
            assert s1 == s2; // lemma ExtensionalityUsingSetInclusion(s1,s2) from lecture 4
        }
    }
}
