include "lecture08.dfy"

// recall some definitions (adding a definition for the totality requirement on the domain of functions,
// and using the type Function (instead of Relation + requiring "ValidFunction") more frequently
ghost predicate ValidFunctionDomain<T1(!new),T2(!new)>(F: Function<T1,T2>, A: iset<T1>) {
    A == Domain(F)
}

// the (infinite) set of natural numbers
ghost const AllNaturalNumbers: iset<nat> := iset n | 0 <= n

// A~B if there exists an injective+surjective (i.e. bijective) F:A->B
ghost predicate CardinallyEquivalentSets<T1(!new),T2(!new)>(A: iset<T1>, B: iset<T2>)
{
    exists F: Function<T1, T2> :: ValidFunctionDomain(F, A) && Range(F) <= B && BijectiveFunction(F, A, B)
}

/*
Claim: The ~ relation is an equivalence relation on the set of all sets
*/
ghost function TheCardinallyEquivalentSetsRelation<T(!new)>(SetOfAllSets: iset<iset<T>>): BinaryRelation<iset<T>,iset<T>>
    ensures RelationOn(TheCardinallyEquivalentSetsRelation(SetOfAllSets), SetOfAllSets)
{
    iset A,B | A in SetOfAllSets && B in SetOfAllSets && CardinallyEquivalentSets(A,B) :: (A,B)
}

lemma TheCardinallyEquivalentSetsRelationIsEquivalenceRelation<T(!new)>(SetOfAllSets: iset<iset<T>>)
    ensures EquivalenceRelation(TheCardinallyEquivalentSetsRelation(SetOfAllSets), SetOfAllSets)
/*
The proof could go as follows:
Reflexivity: A~A for all A
id_A:A-->A the identity function (={(a,a)|a in A}) is injective and surjective

Transitivity: A~B and B~C we need to show A~C
By definition there exist injective and surjective F,G,
F:A-->B
G:B-->C
hence the composition GF is also injective and surjective, hence A~C.

Symmetry: suppose A~B and we need to show B~A

By definition there exists injective and surjective F:A-->B;
and F^-1, the inverse of F, defined as {(b,a)|(a,b) in F}, is injective and surjective F^-1:B-->A, as we'll see below, hence B~A.

a separate (important) lemma: F^-1 of a injective and surjective function, is an injective and surjective function too.

If F is an injective function, F^-1 is a function; and
F:A-->B is injective and surjective, then F^-1:B->A is injective and surjective too.

Proof: 1) suppose F is injective and F^-1 is NOT a function;
there exist (b,a1),(b,a2) in F^-1 s.t. a1!=a2;
but then (a1,b),(a2,b) in F by the definition of F^-1,
and a1!=a2, in contradiction to F being injective.

2) say F:A->B is injective and surjective onto B, and we already know F^-1 is a function.
we aim to show three properties: that (a) dom(F^-1)=B, that (b) it is injective and that (c) it is surjective onto A.

(a) by bi-directional inclusion
if b in dom(F^-1) there exists a s.t. (a,b) in F; since F:A->B, we know b in B;
other direction, suppose b in B, since F is onto B, there exists a in A s.t. (a,b) in F,
hence (b,a) in F^-1, and therefore b in dom(F^-1) as expected.

(b) suppose F^-1 is NOT injective; there exist b1,b2,a s.t. b1!=b2, a in A, and (b1,a),(b2,a) in F^-1;
hemce (a,b1),(a,b2) in F in contradiction to F being a function

(c) F^-1 is onto A: for all a in A, F(a)=b in B and then F^-1(b) = a.

Comments: (F^-1)^-1 = F
          (F^-1) after F = id_A
          F after (F^-1) = id_B

Claim: suppose f:A->B, g:B->A
and say gf=id_A and fg=id_B
then f is injective and surjective, onto B, and g = f^-1 is the inverse of f.

Proof: for being injective, suppose it is NOT, so there exist a1!=a2 both in A and b in B s.t.
f(a1) = f(a2) = b
since gf = id_A we have gf(a1) = a1, hence g(f(a1))=a1 = g(b);
similarly, we have gf(a2) = a2, hence g(f(a2))=a2 = g(b), in contradiction to g being a function (recalling a1!a2 from above)

for f being surjective onto B, since if b in B, consider a in A s.t. a=g(b),
then f(a) = f(g(b)) = fg(b) = b
so we found a in A s.t. f(a)=b

(still need to show g = f^-1 ?)

*/

// A^<n - the set of all sequences of length < "n" (or all functions from [0..i) for any i < n, to range A)
ghost function AllSequencesShorterThan<T(!new)>(n: nat, A: iset<T>): iset<Function<nat, T>> {
    iset Q: Function<nat, T>, m: nat | m < n && ValidSequenceShorterThan(m, Q, A) :: Q
}

ghost predicate ValidSequenceShorterThan<T(!new)>(n: nat, Q: Function<nat, T>, A: iset<T>) {
    var N1: iset<nat> := iset x | x in AllNaturalNumbers && x < n;
    ValidFunctionDomain(Q, N1) && Range(Q) <= A
}

// N^<n - the set of all sequences of natural numbers with length < "n" (or all functions from [0..i) for any i < n, to natural numbers)
ghost function AllNaturalNumberSequencesShorterThan(n: nat): iset<Function<nat, nat>>
{
    AllSequencesShorterThan(n, AllNaturalNumbers)
}

ghost predicate IsFinite<T(!new)>(X: iset<T>)
{
    exists n :: n in AllNaturalNumbers && CardinallyEquivalentSets(X, AllNaturalNumberSequencesShorterThan(n))
}

// sanity checking for our formal definition: show that the empty set is indeed finite
// [it may seem clear, yet on my initial attempt, the definition accepted only non-empty (finite) sets;
// I had to change the "<=" to "<" in the definitions of "AllSequencesShorterThan"]
function ISetOf(A: set): iset { iset a | a in A }
lemma TheEmptySetIsIndeedFinite<T(!new)>(Phi: set<T>)
    requires Phi == {}
    ensures IsFinite(ISetOf(Phi))
{
    var emptySet := ISetOf(Phi);
    var emptySetOfFunctions: iset<Function<nat, nat>> := iset{};
    var emptyBijectiveFunction: Function<T, Function<nat, nat>> := iset{};
    calc {
        IsFinite(emptySet);
    == // by definition
        exists n :: n in AllNaturalNumbers && CardinallyEquivalentSets(emptySet, AllNaturalNumberSequencesShorterThan(n));
    <== { assert 0 in AllNaturalNumbers; }
        CardinallyEquivalentSets(emptySet, AllNaturalNumberSequencesShorterThan(0));
    == { reveal 1; } // see below
        CardinallyEquivalentSets(emptySet, emptySetOfFunctions);
    == // by definition
        exists F: Function<T, Function<nat, nat>> :: ValidFunctionDomain(F, emptySet) && Range(F) <= emptySetOfFunctions && BijectiveFunction(F, emptySet, emptySetOfFunctions);
    <== // our only choice is the empty function
        ValidFunctionDomain(emptyBijectiveFunction, emptySet) && 
        Range(emptyBijectiveFunction) <= emptySetOfFunctions && 
        BijectiveFunction(emptyBijectiveFunction, emptySet, emptySetOfFunctions);
    == // all the involved sets are empty: the empty set is a subset of any set, and the empty relation on an empty set is a bijective function
        true;
    }
    assert 1: AllNaturalNumberSequencesShorterThan(0) == emptySetOfFunctions by {
        calc {
            AllNaturalNumberSequencesShorterThan(0);
        ==
            AllSequencesShorterThan(0, AllNaturalNumbers);
        ==
            iset Q: Function<nat, nat>, m: nat | m < 0 && ValidSequenceShorterThan(m, Q, AllNaturalNumbers) :: Q;
        == // no natural number is < 0
            emptySetOfFunctions;
        }
    }
}

ghost predicate IsCountable<T(!new)>(A: iset<T>) {
    IsFinite(A) || CardinallyEquivalentSets(A, AllNaturalNumbers)
}

lemma CountabilityProperties<T(!new)>(A: iset<T>)
    ensures IsCountable(A) <==> (exists f: Function<T,nat> :: ValidFunctionDomain(f, A) && InjectiveFunction(f))
    ensures IsCountable(A) <==> A == iset{} || (exists g: Function<nat,T> :: ValidFunctionDomain(g, AllNaturalNumbers) && Range(g) <= A && SurjectiveFunction(g, AllNaturalNumbers, A))
/*
top LHS ==> top RHS,
top RHS ==> bottom RHS
bottom RHS ==> top LHS
*/


lemma CartesianProductOfNaturalsOnNaturalsIsCountable()
    ensures IsCountable(CartesianProduct(AllNaturalNumbers, AllNaturalNumbers))

lemma CountabilityOfUnion<T>(A: iset<T>, B: iset<T>)
    requires IsCountable(A) && IsCountable(B)
    ensures IsCountable(A+B)

lemma CountabilityOfCartesianProduct<T1(!new),T2(!new)>(A: iset<T1>, B: iset<T2>)
   requires IsCountable(A) && IsCountable(B)
   ensures IsCountable(CartesianProduct(A, B))

/* Cantor's Theorem */
lemma {:verify true} Cantor1<T(!new)>(A: iset<T>) returns (F1: Function<T, iset<T>>)
    ensures ValidFunctionDomain(F1, A) && Range(F1) <= Powerset(A) && InjectiveFunction(F1)
    ensures !CardinallyEquivalentSets(A, Powerset(A))
{
    F1 := Cantor2(A);
    Cantor3(A);
}

lemma {:verify true} Cantor2<T(!new)>(A: iset<T>) returns (F1: Function<T, iset<T>>)
    ensures ValidFunctionDomain(F1, A) && Range(F1) <= Powerset(A) && InjectiveFunction(F1)
{
    F1 := iset a | a in A :: (a, iset{a});
    assert Domain(F1) == A by {
        assert Domain(F1) <= A by {
            forall a | a in Domain(F1) ensures a in A {
                assert (a, iset{a}) in F1;
                assert a in A;
            }
        }
        assert Domain(F1) >= A by {
            assert forall a :: a in A ==> (a, iset{a}) in F1;
        }
    }
    assert Range(F1) <= Powerset(A);
    assert InjectiveFunction(F1) by {
        assert forall x1,x2,y1,y2 :: (x1,y1) in F1 && (x2,y2) in F1 && x1 != x2 ==> y1 == iset{x1} != iset{x2} == y2;
    }
}

lemma {:verify true} Cantor3<T(!new)>(A: iset<T>)
    ensures !CardinallyEquivalentSets(A, Powerset(A))
{
    var B := Powerset(A);
    calc {
        !CardinallyEquivalentSets(A, Powerset(A));
    == // by definition
        !exists F: Function<T, iset<T>> :: ValidFunctionDomain(F, A) && Range(F) <= B && BijectiveFunction(F, A, B);
    == // negation of quantifiers 
        forall F: Function<T, iset<T>> :: !(ValidFunctionDomain(F, A) && Range(F) <= B && BijectiveFunction(F, A, B));
    == // De Morgan
        forall F: Function<T, iset<T>> :: !(ValidFunctionDomain(F, A) && Range(F) <= B) || !BijectiveFunction(F, A, B);
    == // rewriting as implication
        forall F: Function<T, iset<T>> :: ValidFunctionDomain(F, A) && Range(F) <= B ==> !BijectiveFunction(F, A, B);
    }
    forall F: Function<T, iset<T>> | ValidFunctionDomain(F, A) && Range(F) <= B ensures !BijectiveFunction(F, A, B) {
        calc {
            BijectiveFunction(F, A, B);
        == // by definition
            InjectiveFunction(F) && SurjectiveFunction(F, A, B);
        ==> // forall P,Q :: P && Q ==> Q
            SurjectiveFunction(F, A, B);
        == { Cantor4(F, A, B); }
            false; // contradiction (to the assumption that F is bijective)
        }
    }
}

lemma {:verify true} Cantor4<T(!new)>(F: Function<T, iset<T>>, A: iset<T>, B: iset<iset<T>>)
    requires ValidFunctionDomain(F, A) && B == Powerset(A) && Range(F) <= B
    ensures !SurjectiveFunction(F, A, B)
{
    calc {
        !SurjectiveFunction(F, A, B);
    == { EquivalentSurjectiveDefinitions(F, A, B); }
        !SurjectiveFunction'(F, A, B);
    == // by definition
        Range(F) != B;
    == { assert Range(F) <= B; } // from the precondition
        Range(F) < B;
    == { Cantor5(F, A, B); }
        true;
    }
}

// and finally this is the essence of Cantor's theorem
lemma {:verify true} Cantor5<T(!new)>(F: Function<T, iset<T>>, A: iset<T>, B: iset<iset<T>>)
    requires ValidFunctionDomain(F, A) && B == Powerset(A) && Range(F) <= B
    ensures Range(F) < B
{
    // we need to show there's at least on element of B not in the range of F
    assert exists X :: X in B && X !in Range(F) by {
        // on the lines of Cantor's diagonalization argument: the following is a set
        // containing all elements a0 of A not being members of their own image in F
        var X := iset a0, F_of_a0 | a0 in A && (a0, F_of_a0) in F && a0 !in F_of_a0 :: a0;
        assert X in B;
        assert X !in Range(F) by {
            // this set cannot be in the range of F since it is different from any element of that range
            // (being a subset of A) with repect to at least one member of A 
            forall a0, F_of_a0 | a0 in A && (a0, F_of_a0) in F ensures F_of_a0 != X {
                if a0 in X // the assertions below are for the human reader only: this "if" is enough for Dafny to complete the proof by itself
                {
                    assert In_X_1: a0 in X;                             // by the guard
                    assert In_X_2: a0 !in F_of_a0 by { reveal In_X_1; } // and by the definition of X
                    assert F_of_a0 != X by { reveal In_X_1, In_X_2; }   // and by the extensionality axiom
                }
                else
                {
                    assert Not_In_X_1: a0 !in X;                                           // negation of the guard
                    assert Not_In_X_2: a0 in A && (a0, F_of_a0) in F;                      // by choice of a0
                    assert Not_In_X_3: a0 in F_of_a0 by { reveal Not_In_X_1, Not_In_X_2; } // and by the definition of X
                    assert F_of_a0 != X by { reveal Not_In_X_1, Not_In_X_3; }              // and by the extensionality axiom
                }
            }
        }
    }
}

// here's the same lemma again, with a shorter proof, stating only what helps Dafny complete the proof
lemma {:verify true} Cantor5'<T(!new)>(F: Function<T, iset<T>>, A: iset<T>, B: iset<iset<T>>)
    requires ValidFunctionDomain(F, A) && B == Powerset(A) && Range(F) <= B
    ensures Range(F) < B
{
    var X := iset a0, F_of_a0 | a0 in A && (a0, F_of_a0) in F && a0 !in F_of_a0 :: a0; // Cantor's Diagonalization
    assert X in B-Range(F) by {
        forall a0, F_of_a0 | a0 in A && (a0, F_of_a0) in F ensures F_of_a0 != X {
            assert a0 in X ==> F_of_a0 != X;
        }
    }
}

lemma CantorForNaturalNumbers() returns (F1: Function<nat, iset<nat>>)
    ensures ValidFunctionDomain(F1, AllNaturalNumbers) && Range(F1) <= Powerset(AllNaturalNumbers) && InjectiveFunction(F1)
    ensures !CardinallyEquivalentSets(AllNaturalNumbers, Powerset(AllNaturalNumbers))
{
    F1 := Cantor1(AllNaturalNumbers);
}

lemma PowersetOfNaturalNumbersIsNotCountable()
    ensures !IsCountable(Powerset(AllNaturalNumbers))

ghost const AllRealNumbers := iset x: real | true

lemma TheRealsAreNotCountable()
    ensures !IsCountable(AllRealNumbers)

lemma CardinalEquivalenceOfRealAndThePowersetOfTheNaturals()
    ensures CardinallyEquivalentSets(AllRealNumbers, Powerset(AllNaturalNumbers))
