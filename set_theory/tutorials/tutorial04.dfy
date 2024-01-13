include "../lectures/lecture04.dfy"

lemma {:verify true} Distributivity2'(A: set, B: set, C: set, L: set, R: set)
	requires Pre1: L == A*(B+C)
	requires Pre2: R == A*B+A*C
	ensures R <= L
{
	forall x | x in R ensures x in L {
		calc {
			x in R;
		== { reveal Pre2; }
			x in A*B+A*C;
		==> { Distributivity2a(A, B, C, x); }
			x in A*(B+C);
		== { reveal Pre1; }
			x in L;
		}
	}
}

lemma {:verify true} Distributivity2a<T>(A: set<T>, B: set<T>, C: set<T>, x: T)
	ensures x in A*(B+C) ==> x in A*B+A*C
{
	if x in A*(B+C)
	{
		assert 1: x in A; // from the guard and the definition of set intersection
		assert 2: x in B+C; // again, from the guard and the definition of set intersection
		if x in B
		{
			assert 3: x in A && x in B by { reveal 1; } // and from the guard
			assert 4: x in A*B by { reveal 3; } // and by the definition of set intersection
			assert x in A*B+A*C by { reveal 4; } // and by the definition of set union
		}
		else
		{
			assert 5: x !in B; // from the negation of the guard
			assert 6: x in B || x in C by { reveal 2; } // and by the definition of set union
			assert 7: x in C by { reveal 5,6; }
			assert 8: x in A*C by { reveal 1,7; }
			assert x in A*B+A*C by { reveal 8; } // and by the definition of set union
		}
		assert x in A*B+A*C;
	}
}

method M4a() {
	var R: iset<real> := iset x: real | true;
	var R1: iset<real> := iset x: real | 0.0 <= x < 1.0;
	var R2: iset<real> := iset x: real | 1.0 <= x < 2.0;
	assert R1 <= R;
	assert R2 <= R;
	assert !(R2 <= R1) by { assert 1.0 in R2 && 1.0 !in R1; }
	assert R1*R2 == iset{};
	var N: iset<nat> := iset n: int | n >= 0;
	var AllNaturalNumbers_AsReals := iset n: nat :: n as real;
	assert AllNaturalNumbers_AsReals*R == AllNaturalNumbers_AsReals;
}