//include "../predicate_logic.dfy"

/*

Logic and Set Theory - lecture 9

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ Predicate logic as a formal language

Today:
∙ Proof theory of predicate logic: Natural deduction rules


2.3 Proof theory of predicate logic

2.3.1 Natural deduction rules

∙ equality introduction

	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  =i                        (reflexivity of "=")
	    t = t    

∙ equality elimination

	t1 = t2       φ[t1/x]	
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  =e
	       φ[t2/x]       

Convention 2.10  When we write a substitution in the form φ[t/x],
we implicitly assume that t is free for x in φ; for, as we
saw in the last section, a substitution doesn’t make sense otherwise.

- example proof for the sequent:

	(x + 1) = (1 + x), (x + 1 > 1) ⟶ (x + 1 > 0) ⊦ (1 + x) > 1 ⟶ (1 + x) > 0

	1    (x + 1) = (1 + x)              premise
	2    (x + 1 > 1) ⟶ (x + 1 > 0)     premise
	3    (1 + x > 1) ⟶ (1 + x > 0)     =e 1,2 [with φ being (x > 1) ⟶ (x > 0)]

In this particular proof t1 is (x + 1), t2 is (1 + x) and φ is (x > 1) ⟶ (x > 0).

Since
	((x > 1) ⟶ (x > 0))[(x + 1) / x]
=
	((x + 1 > 1) ⟶ (x + 1 > 0))

and

	((x > 1) ⟶ (x > 0))[(1 + x) / x]
=
	((1 + x > 1) ⟶ (1 + x > 0))

Note that = is a binary relation: we write <t1,t2> is in the set R= in infix notation t1 = t2

		t1 = t2 ⊦ t2 = t1                     (Symmetry of "=")
		t1 = t2, t2 = t3 ⊦ t1 = t3            (Transitivity of "=")


- A proof for the symmetry of "=":

	1    t1 = t2        premise
	2    t1 = t1        =i
	3    t2 = t1        =e 1,2 [φ is "x = t1"]


- A proof for the transitivity of "=":

	1    t2 = t3        premise
	2    t1 = t2        premise
	3    t1 = t3        =e 1,2 [φ is "t1 = x"]

since

	(t1 = x)[t2 / x]
=
	(t1 = t2)

and indeed this is what we already have in line 2; and the conclusion:

	(t1 = x)[t3 / x]
=
	(t1 = t3)


The proof rules for universal quantification


∙ forall elimination

	    ∀x φ	
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∀e
	   φ[t/x]       

Example 2.11 To see the necessity that t be free for x in φ:

		φ
	=
		∃y (x < y)
	
	
		φ[y/x]
	=
		∃y (y < y)
		
	A possible solution: use a fresh variable for y:

		φ'
	=
		∃z (x < z)

		φ'[y/x]
	=
		∃z (y < z)


∙ forall introduction

	┌───────────┐
	│ x0        │  
	│           │
	│      ∙    │
	│      ∙    │
	│      ∙    │
	│           │ 
	│   φ[x0/x] │
	└───────────┘
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∀i
	    ∀x φ

Here is a proof of the sequent:

	∀x (P(x) ⟶ Q(x)), ∀x P(x) ⊢ ∀x Q(x)


	1         ∀x (P(x) ⟶ Q(x))  premise
	2         ∀x P(x)            premise
	    ┌────────────────────────────────┐
	3   │ x0  P(x0) ⟶ Q(x0)     ∀e 1
	4   │     P(x0)              ∀e 2
	5   │     Q(x0)              ⟶e 4,3
	    └────────────────────────────────┘
	6         ∀x Q(x)            ∀i 3−5


Here is a simpler example which uses only ∀e: we show the validity of
the sequent

	P(t), ∀x (P(x) ⟶ ¬Q(x)) ⊢ ¬Q(t)

for any term t:

	1         P(t)                premise
	2         ∀x (P(x) ⟶ ¬Q(x))  premise
	3         P(t) ⟶ ¬Q(t)       ∀e 2
	4         ¬Q(t)               ⟶e 1,3


The proof rules for existential quantification


∙ exists introduction

	   φ[t/x]
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∃i
	    ∃x φ       

∙ exists elimination

	        ┌─────────────┐
	        │ x0  φ[x0/x] │  
	        │             │
	        │        ∙    │
	        │        ∙    │
	        │        ∙    │
	        │             │ 
	        │        χ    │
	∃x φ    └─────────────┘
	⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯  ∃e
	           χ

Of course, we impose the side condition that x0 can’t occur outside its box
(therefore, in particular, it cannot occur in χ). The box is controlling two
things: the scope of x0 and also the scope of the assumption φ[x0/x].

- example proof: validity of the sequent

	∀x φ ⊢ ∃x φ

	1    ∀x φ      premise
	2    φ[x/x]    ∀e 1
	3    ∃x φ      ∃i 2

- a more complicated proof example, for validity of the sequent

	∀x (P(x) ⟶ Q(x)), ∃x P(x) ⊢ ∃x Q(x)


	1         ∀x (P(x) ⟶ Q(x))  premise
	2         ∃x P(x)            premise
	    ┌───────────────────────────────────┐
	3   │ x0  P(x0)              assumption
	4   │     P(x0) ⟶ Q(x0)     ∀e 1
	5   │     Q(x0)              ⟶e 3,4
	6   │     ∃x Q(x)            ∃i 5
	    └───────────────────────────────────┘
	7         ∃x Q(x)            ∃e 2,3−6


- an almost identical example of an illegal ‘proof’:

	1         ∀x (P(x) ⟶ Q(x))  premise
	2         ∃x P(x)            premise
	    ┌───────────────────────────────────┐
	3   │ x0  P(x0)              assumption
	4   │     P(x0) ⟶ Q(x0)     ∀e 1
	5   │     Q(x0)              ⟶e 3,4
	    └───────────────────────────────────┘
	6         Q(x0)              ∃e 2,3−5
	7         ∃x Q(x)            ∃i 6

Line 6 allows the fresh parameter x0 to escape the scope of the
box which declares it. We will see later (*) an example where
such illicit use of proof rules results in unsound arguments.

- a sequent with a slightly more complex proof:

	∀x (Q(x) ⟶ R(x)), ∃x (P(x) ∧ Q(x)) ⊢ ∃x (P(x) ∧ R(x))


	1         ∀x (Q(x) ⟶ R(x))  premise
	2         ∃x (P(x) ∧ Q(x))   premise
	    ┌───────────────────────────────────┐
	3   │ x0  P(x0) ∧ Q(x0)      assumption
	4   │     Q(x0) ⟶ R(x0)     ∀e 1
	5   │     Q(x0)              ∧e2 3
	6   │     R(x0)              ⟶e 5,4
	7   │     P(x0)              ∧e1 3
	8   │     P(x0) ∧ R(x0)      ∧i 7,6
	9   │     ∃x (P(x) ∧ R(x))   ∃i 8
	    └───────────────────────────────────┘
	10        ∃x (P(x) ∧ R(x))   ∃e 2,3−9


	The rules ∀i and ∃e both have the side condition that the dummy variable
cannot occur outside the box in the rule. Of course, these rules may still be
nested, by choosing another fresh name (e.g. y0) for the dummy variable. For
example, consider the sequent ∃x P(x), ∀x ∀y (P(x) ⟶ Q(y)) ⊢ ∀y Q(y).
(Look how strong the second premise is, by the way: given any x, y, if P(x),
then Q(y). This means that, if there is any object with the property P, then
all objects shall have the property Q.) Its proof goes as follows: We take an
arbitrary y0 and prove Q(y0); this we do by observing that, since some x
satisfies P, so by the second premise any y satisfies Q:

	1         ∃x P(x)               premise
	2         ∀x ∀y (P(x) ⟶ Q(y))  premise
	     ┌──────────────────────────────────────┐
	3    │  y0
	     │┌────────────────────────────────────┐
	4    ││ x0  P(x0)               assumption
	5    ││     ∀y (P(x0) ⟶ Q(y))  ∀e 2
	6    ││     P(x0) ⟶ Q(y0)      ∀e 5
	7    ││     Q(y0)               ⟶e 4,6
	     │└────────────────────────────────────┘
	8    │      Q(y0)               ∃e 1,4−7
	     └──────────────────────────────────────┘
	9           ∀y Q(y)             ∀i 3−8


(*) an illegal ‘proof’ of an invalid sequent:

	∃x P(x), ∀x (P(x) ⟶ Q(x)) ⊢? ∀y Q(y)


	1         ∃x P(x)               premise
	2         ∀x (P(x) ⟶ Q(x))     premise
	     ┌──────────────────────────────────────┐
	3    │  x0
	     │┌────────────────────────────────────┐
	4    ││ x0  P(x0)               assumption
	5    ││     P(x0) ⟶ Q(x0)      ∀e 2
	6    ││     Q(x0)               ⟶e 4,5
	     │└────────────────────────────────────┘
	7    │      Q(x0)               ∃e 1,4−6
	     └──────────────────────────────────────┘
	8           ∀y Q(y)             ∀i 3−7

*/
module Logic_09 {}