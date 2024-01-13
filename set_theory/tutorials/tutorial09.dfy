include "../lectures/lecture09.dfy"

/*
נגדיר את
 A 
 להיות קבוצת המספרים הטבעיים הזוגיים ואת 
 B 
 להיות קבוצת המספרים הטבעיים האי-זוגיים, בשפת דפני:
 */
ghost const A := iset x: nat | x%2 == 0
ghost const B := iset y: nat | y%2 == 1
/*
באמצעות מי מבין הקבוצות הבאות ניתן להוכיח שהקבוצה 
A
 שקולה עוצמתית לקבוצה 
 B
 ?


 F : A -> B

*/
ghost const Fa := iset x, y | x in A && y in B && x+1 == y :: (x,y) // looks correct!
ghost const Fb := iset x, y | x in A && y in B && x == y+1 :: (x,y) // Correct answer? No: 0 !in Domain(Fb)
ghost const Fc := iset x, y | x in A && y in B && x-1 == y :: (x,y) // 0 !in Domain(Fc)
ghost const Fd := iset x, y | x in A && y in B && x == y-1 :: (y,x) // domain is B, not A

method Solution()
{
	assert CardinallyEquivalentSets(A, B) by {
		var F := Lemma1();
		assert ValidFunctionDomain(F, A) && Range(F) <= B && BijectiveFunction(F, A, B);
	}

	assert (6,5) in Fb;
	assert (2,1) in Fb;
	assert (0,-1) !in Fb by { assert -1 !in B; }
	assert forall y :: y in B ==> (0,y) !in Fb;
	assert 0 !in Domain(Fb);
}

lemma Lemma1() returns (F: Function<nat, nat>)
	ensures ValidFunctionDomain(F, A) && Range(F) <= B && BijectiveFunction(F, A, B)
{
	F := Fa; // we believe this is the correct answer; let's try to prove:
	assert ValidFunctionDomain(F, A) by {
		assert Domain(F) == A by {
			assert Domain(F) <= A by { assert forall x,y :: (x,y) in F ==> x in A && y in B && x+1 == y; }
			assert Domain(F) >= A by {
				forall x | x in A ensures exists y :: y in B && (x,y) in F {
					assert x in A;
					assert x >= 0 && x%2 == 0;
					var y': nat := x+1;
					assert y' >= 1 && y'%2 == 1;
					assert y' in B && (x,y') in F;
				}
			}
		}
	}
	assert Range(F) <= B;
	assert BijectiveFunction(F, A, B) by {
		assert A == Domain(F);
		assert Range(F) <= B;
		assert InjectiveFunction(F);
		assert SurjectiveFunction(F, A, B) by {
			assert ValidFunction(F);
			assert A == Domain(F);
			assert Range(F) <= B;
			assert forall y :: y in B ==> exists x :: x in A && (x,y) in F by {
				forall y: nat | y in B ensures exists x :: x in A && (x,y) in F {
					assert y in B;
					assert y%2 == 1;
					var x': nat := y-1;
					assert x' == y-1;
					assert x'%2 == 0;
					assert y >= 1;
					assert x' >= 0;
					assert x' in A;
					assert x'+1 == y-1+1 == y;
					assert (x',y) in F;
				}
			}	
		}
	}
}