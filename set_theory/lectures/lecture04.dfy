/*

Lecture 4: more on proving correctness of properties from set theory

- proving set equality: extensionality axiom / bidirectional inclusion
- proof by contradiction
- proving bidirectional equivalence (logical equivalence, if-and-only-if, iff): ((L ==> R) && (L <== R)), ((L ==> R) && (!L ==> !R))
- proof by calculation: the "calc" construct
- distributivity

Further reading about "Different Styles of Proofs" in Dafny by Rustan Leino: http://leino.science/papers/krml276.html

*/

include "lecture03.dfy"

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

lemma EmptySet(A: set)
    ensures A=={} <==> (forall x :: x !in A)
{}

/*
the empty set is unique

for any two sets A,B,
if for any element a, a is not a member of A,
and if for any element b, b is not a member of B,
then the sets A and B are equal.
*/
lemma EmptySets(A: set, B: set)
    requires Pre1: forall a :: a !in A
    requires Pre2: forall b :: b !in B
    ensures A == B
{
    // Dafny accepts this (when there are no labels on the preconditions), still here's a proof (by contradiction)
    assert Alef: forall x :: x in A ==> x in B by {
        forall x | x in A ensures x in B {
            assert Alef1: x in A;
            if x !in B
            {
                assert Alef2: x !in A by { reveal Pre1; }
                assert false by {
                    assert x in A && x !in A by { reveal Alef1,Alef2; }
                }
            }
        }
    }
    assert Bet: forall x :: x in B ==> x in A by {
        forall x | x in B ensures x in A { // similar to the above, written more directly
            assert Bet1: x in B;
            assert Bet2: false by {
                assert x in B && x !in B by { reveal Bet1,Pre2; }
            }
            assert x !in B by { reveal Bet2; } // false implies anything
        }
    }
    assert Gimel: forall x :: x in A <==> x in B by { reveal Alef,Bet; }
    assert A == B by { reveal Gimel; ExtensionalityAxiom(A, B); }
}

// proving bidirectional implication (logical equivalence, if-and-only-if, iff): L ==> R, R ==> L
/*

(P <==> Q) == ((P ==> Q) && (P <== Q))

 P  Q  (P <==> Q)   (P ==> Q)      (P <== Q))          ((P ==> Q) && (P <== Q))
 F  F  T            T              T                   T
 F  T  F            T              F                   F
 T  F  F            F              T                   F
 T  T  T            T              T                   T
*/
lemma BidirectionImplication(P: bool, Q: bool)
    ensures (P <==> Q) == ((P ==> Q) && (P <== Q))
{}

/*
one more way of proving logical equivalence L <==> R:
prove L ==> R and prove !L ==> !R

(P <==> Q) == ((P ==> Q) && (!P ==> !Q))

exercise: verify correctness using a truth table; we'll prove it in a different way:

(P <==> Q)
==
((P ==> Q) && (P <== Q))
==
((P ==> Q) && (P || !Q))
== // double negation
((P ==> Q) && (!!P || !Q))
==
((P ==> Q) && (!P ==> !Q))

such chains of equalities can be written in Dafny with the "calc" construct:
*/
lemma BidirectionImplicationWithNegation(P: bool, Q: bool)
    ensures (P <==> Q) == ((P ==> Q) && (!P ==> !Q))
{ // w/H: rewrite using our new datatype?
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

// an alternative formulation for the extensionality axiom:
lemma {:verify true} ExtensionalityUsingSetInclusion(A: set, B: set)
    requires 1: A <= B
    requires 2: B <= A
    ensures A == B
{
    // when the proof is partial (a draft), we write "{:verify false}"
    // between the keyword "lemma" and the lemma's name, asking Dafny
    // NOT to try an verify correctness of this lemma; as soon as we
    // complete the proof, we turn the "false" into "true" or remove the
    // {:verify false} clause altogether
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

lemma DistributivityOfSetIntersectionOverSetUnion(A: set, B: set, C: set)
    ensures A*(B+C) == A*B+A*C
{
    var L, R := A*(B+C), A*B+A*C;
    assert LsubsetR: L <= R by { Distributivity1(A, B, C, L, R); }
    assert RsubsetL: R <= L by { Distributivity2(A, B, C, L, R); }
    assert L == R by { reveal LsubsetR, RsubsetL; ExtensionalityUsingSetInclusion(L, R); }
}

lemma Distributivity1(A: set, B: set, C: set, L: set, R: set)
    requires Pre1: L == A*(B+C)
    requires Pre2: R == A*B+A*C
    ensures L <= R
{
    forall x | x in L ensures x in R {
        calc {
            x in L;
        == { reveal Pre1; }
            x in A*(B+C);
        ==> { Distributivity1a(A, B, C, x); }
            x in A*B+A*C;
        == { reveal Pre2; }
            x in R;
        }
    }
}

lemma Distributivity1a<T>(A: set<T>, B: set<T>, C: set<T>, x: T)
    requires Pre: x in A*(B+C)
    ensures x in A*B+A*C
{
    assert x in A by { reveal Pre; } // and by definition of intersection
    assert x in B+C by { reveal Pre; } // and again by definition of intersection
    if x in B
    {
        assert x in A && x in B;
        assert x in A*B; // by the assertion above and the definition of set intersection
        assert x in A*B+A*C; // by the assertiojn above and the definition of set union
    } 
    else
    {
        assert x in C; // by definition of set union
        assert x in A && x in C;
        assert x in A*C; // by the assertion above and the definition of set intersection
        assert x in A*B+A*C; // by the assertion above and the definition of set union
    }
}

// this could be proved in a similar way to Distributivity1 (see tutorial04)
lemma Distributivity2(A: set, B: set, C: set, L: set, R: set)
    requires L == A*(B+C) && R == A*B+A*C
    ensures R <= L
{}

// is this true too? in integer arithmetic it is NOT true! for example 1+(2*3) != (1+2)*(1+3))
lemma DistributivityOfSetUnionOverSetIntersection(A: set, B: set, C: set)
    ensures A+(B*C) == (A+B)*(A+C)
{}
