/*

Logic and Set Theory - lecture 2

Today: introduction to set theory + first proofs using Dafny

- three ways to define a set: extensional, intentional (set comprehension), through operations on existing sets
- cardinality
- operations on sets: union, intersection, difference, complement
- set inclusion (subsets)
- a first look on the negation of a quantifier
*/

include "lecture01.dfy"

module Lecture02 {
	import opened Lecture01

	// but first, in continuation to lecture 1: logical implication
	/*

	The truth table of implication (-->, in Dafny ==>):

	P  Q  !P    (!P || Q)
	F  F  T     T
	F  T  T     T
	T  F  F     F
	T  T  F     T

	we can define logical implication as "(!P || Q)", such that (!P || Q) == (P --> Q)
	P  Q  (P --> Q)
	F  F  T
	F  T  T
	T  F  F
	T  T  T

	*/

	// set theory:
	const s1 := {1, 9, 4} // extensional definition of a set
	const s2 := {4, 9, 1, 4, 1}
	const s3 := {1, 4}

	method M1()
	{
		assert !(1 == 2);
		assert 1 != 2;
		assert s1 == {4, 9, 1} == s2;
		assert |s1| == |s2| && |s2| == 3; // short version: |s1| == |s2| == 3;
		assert 4 in s1; // set membership
		assert !(8 in s1);
		assert 8 !in s1;

		assert !(s3 == s1) by {
			assert 9 in s1 && 9 !in s3;
		}
	}

	const AllEvenNumbersBetween100And200 := set n: int | 100 <= n <= 200 && n%2 == 0 // {100, 102, 104, 106, ..., 200}

	method M2()
	{
		assert 158 in AllEvenNumbersBetween100And200;
		assert 159 !in AllEvenNumbersBetween100And200 by { assert 159%2 != 0; }
		assert 58 !in AllEvenNumbersBetween100And200 by { assert 58 < 100; } 
		assert 1580 !in AllEvenNumbersBetween100And200 by { assert 200 < 1580; }
		assert -159 !in AllEvenNumbersBetween100And200 by { assert -159 < 100; }
		assert -159 !in AllEvenNumbersBetween100And200 by { assert -159%2 != 0; }
		//assert 104.5 !in AllEvenNumbersBetween100And200; // in Dafny, sets are defined on elements of the same type; in theory, sets of different types are allowed
	}

	// a first operation on sets: union
	const s4 := {"abc", "def"}
	const s5 := {"abc", "ert"}
	const s6 := s4+s5
	//const s6' := set str: string | str in s4 || str in s5 // later in the semester we will work with infinite sets, and learn how to make this compile

	method M3() {
		assert "abc" != "ABC"; // strings in Dafny are case sensitive
		assert "abc" != "bac"; // the order of characters in a string matters
		assert {'a', 'b', 'c'} == {'b', 'a', 'c'};
		assert "" !in s6;
		assert "ABC" !in s6;
		assert "abc" in s6;
		assert "def" in s6;
		assert "ert" in s6;
		assert s6 == {"abc", "def", "ert"};
		// "forall" is a quantifier ("כמת"), generalizing conjunction (&&)
		assert forall str: string :: (str in s6) <==> (str in s4) || (str in s5);
	}

	lemma SetUnionLemma(A: set<string>, B: set<string>, C: set<string>)
		requires C == A+B
		ensures forall str: string :: (str in C) <==> (str in A) || (str in B)
	{}

	lemma SetUnionLemma'<T>(A: set<T>, B: set<T>, C: set<T>)
		requires C == A+B
		ensures forall str :: (str in C) <==> (str in A) || (str in B)
	{}

	lemma SetUnionLemma''(A: set, B: set, C: set)
		requires C == A+B
		ensures forall e :: (e in C) <==> (e in A) || (e in B)
	{}

	ghost function SetUnion<T(!new)>(A: iset<T>, B: iset<T>): iset<T> {
		iset x: T | x in A || x in B
	}

	// operations on sets: intersection

	const s7 := s4*s5
	const s7' := set str: string | str in s4 && str in s5

	method M4()
	{
		assert "" !in s7;
		assert "ABC" !in s7;
		assert "abc" in s7;
		assert "def" !in s7 by { assert "def" !in s5 && s7 == s4*s5; }
		assert "ert" !in s7 by { assert "ert" !in s4 && s7 == s4*s5; }
		assert s7 == {"abc", "def"}*{"abc", "ert"} == {"abc"};
		assert forall str: string :: (str in s7) <==> (str in s4) && (str in s5);
		assert s7' == s7;
	}

	lemma SetIntersectionLemma(A: set<string>, B: set<string>, C: set<string>)
		requires C == A*B
		ensures forall str: string :: (str in C) <==> (str in A) && (str in B)
	{}

	function SetIntersection(A: set, B: set): set {
		set x | x in A && x in B
	}

	ghost const s7'' := SetIntersection(s4, s5)

	method M5() {
		assert s7'' == s7' == s7;
	}

	// operations on sets: difference

	const s8 := {9}

	method M6a() {
		assert s1 ==  {1, 9, 4} && s3 == {1, 4}; // recall earlier definitions
		assert s8 == s1-s3;
	}

	function SetDifference(A: set, B: set): set {
		set y | y in A && y !in B
	}

	// operations on sets: complement (later in the semester)

	// set inclusion (subsets):

	const s9 := {"def"}

	method M6() {
		assert s9 <= s4; // s8 is a subset of s4
		assert !(s9 <= s5) by { assert "def" in s9 && "def" !in s5; }
		assert !(s9 <= s5) by { assert "def" in s9-s5; }
		assert s9 == s4-s5;
	}

	// claim: the intersection of two sets is a subset of both
	lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
		requires C == SetIntersection(A, B) // == A*B
		ensures C <= A && C <= B
	{}

}