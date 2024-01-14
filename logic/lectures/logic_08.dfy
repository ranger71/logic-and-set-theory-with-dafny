include "../predicate_logic.dfy"

/*

Logic and Set Theory - lecture 8

R. Ettinger (ettinger.ran@iac.ac.il)
Online office hours: Tuesdays 18-19

Textbook: Logic in Computer Science: Modelling and Reasoning about Systems (2nd edition) by Huth and Ryan.

Last week:
∙ Completeness of Propositional Logic
∙ Semantic equivalence; step-by-step proof by calculation in Dafny
∙ "Debugging" proofs (of natural deduction) in Dafny
∙ Introduction to predicate logic

Today:
∙ Predicate logic as a formal language


2.2 Predicate logic as a formal language

2.2.1 Terms

Definition 2.1 Terms are defined as follows.

∙ Any variable is a term.
∙ If c ∈ F is a nullary function, then c is a term.
∙ If t1, t2, ... , tn are terms and f ∈ F has arity n > 0, then f(t1, t2, ... , tn) is a term.
∙ Nothing else is a term.

*/
module Logic_08 {
	import opened PredicateLogic

	const Term_Example_2_2 := F("g", [F("f", [VAR("n")]), VAR("n")]) // "g(f(n), n)"

/*
Definition 2.3 We define the set of formulas over (F,P) inductively, using
the already defined set of terms over F:

∙ If P' ∈ P is a predicate symbol of arity n ≥ 1, and if t1, t2, ... , tn are terms over
  F, then P'(t1, t2, ... , tn) is a formula.
∙ If φ is a formula, then so is (¬φ).
∙ If φ and ψ are formulas, then so are (φ ∧ ψ), (φ ∨ ψ) and (φ ⟶ ψ).
∙ If φ is a formula and x is a variable, then (∀x φ) and (∃x φ) are formulas.
∙ Nothing else is a formula.

Convention 2.4 For convenience, we retain the usual binding priorities
agreed upon in Convention 1.3 and add that ∀y and ∃y bind like ¬. Thus,
the order is:

∙ ¬, ∀y and ∃y bind most tightly;
∙ then ∨ and ∧;
∙ then ⟶, which is right-associative.

We also often omit brackets around quantifiers, provided that doing so introduces no ambiguities.

Here's a formula with the parse tree in Figure 2.1:

	∀x ((P(x) ⟶ Q(x)) ∧ S(x, y))

*/

	const f_2_1 := FORALL("x", AND(IMPLIES(P("P",[x]), P("Q",[x])), P("S",[x, y])))

/*

2.2.3 Free and bound variables

Consider the formula:

	P(c) ∧ ∀y (P(y) ⟶ Q(y)) ⟶ Q(c)

for a constant "c"; clearly, this formula should be true no matter what model(*) we are looking at;
later we'll learn how to prove such properties (section 2.3)

(*) a model for a given formula includes a concrete definition for all functions and predicates in that formula

*/
	const f_page_102 := IMPLIES(AND(P("P", [F("c", [])]), FORALL("y", IMPLIES(P("P",[y]), P("Q",[y])))), P("Q",[F("c", [])]))

/*

Recall f_2_1:

	∀x ((P(x) ⟶ Q(x)) ∧ S(x, y))

We draw parse trees in the same way as for propositional formulas, but with two additional sorts of nodes: for quantifiers and predicate expressions.

In our example in Figure 2.1, we have three leaf nodes x. If we walk up the
tree beginning at any one of these x leaves, we run into the quantifier ∀x. This
means that those occurrences of x are actually "bound" to ∀x so they represent,
or stand for, any possible value of x.

2. In walking upwards, the only quantifier that the leaf node y runs into is ∀x but
that x has nothing to do with y; x and y are different place holders. So y is free
in this formula. This means that its value has to be specified by some additional
information, for example, the contents of a location in memory.


Definition 2.6 Let φ be a formula in predicate logic. An occurrence of x
in φ is free in φ if it is a leaf node in the parse tree of φ such that there
is no path upwards from that node x to a node ∀x or ∃x. Otherwise, that
occurrence of x is called bound. For ∀x φ, or ∃x φ, we say that φ – minus
any of φ’s subformulas ∃x ψ, or ∀x ψ – is the scope of ∀x, respectively ∃x.

Thus, if x occurs in φ, then it is bound if, and only if, it is in the scope of
some ∃x or some ∀x; otherwise it is free. In terms of parse trees, the scope
of a quantifier is just its subtree, minus any subtrees which re-introduce a
quantifier for x; e.g. the scope of ∀x in ∀x (P(x) ⟶ ∃x Q(x)) is P(x).

It is quite possible, and common, that a variable is bound and free in a formula.

Consider the formula

	(∀x (P(x) ∧ Q(x))) ⟶ (¬P(x) ∨ Q(y))

and its parse tree in Figure 2.2.

*/
	const f_2_2 := IMPLIES(FORALL("x", AND(P("P",[x]), P("Q",[x]))), OR(NOT(P("P",[x])), P("Q",[y])))


/*
The two x leaves in the subtree of ∀x are
bound since they are in the scope of ∀x, but the leaf x in the right subtree of
⟶ is free since it is not in the scope of any quantifier ∀x or ∃x. Note, however,
that a single leaf either is under the scope of a quantifier, or it isn’t. Hence
individual occurrences of variables are either free or bound, never both at
the same time.


2.2.4 Substitution

Definition 2.7 Given a variable x, a term t and a formula φ we define φ[t/x]
to be the formula obtained by replacing each free occurrence of variable x
in φ with t.

Definition 2.8 Given a term t, a variable x and a formula φ, we say that
t is free for x in φ if no free x leaf in φ occurs in the scope of ∀y or ∃y for
any variable y occurring in t.


Example 2.9 Consider the φ with parse tree in Figure 2.4 and let t be
f(y, y). All two occurrences of x in φ are free. The leftmost occurrence of
x could be substituted since it is not in the scope of any quantifier, but
substituting the rightmost x leaf introduces a new variable y in t which
becomes bound by ∀y. Therefore, f(y, y) is not free for x in φ.

*/
	const zero := F("0", [])
	const one := F("1", [])
	const x_plus_one := F("+", [x, one])
	const one_plus_x := F("+", [one, x])
	const x_plus_one_eq_one_plus_x := P("=", [x_plus_one, one_plus_x])
	const x_plus_one_gt_one := P(">", [x_plus_one, one])
	const x_plus_one_gt_zero := P(">", [x_plus_one, zero])
	const one_plus_x_gt_one := P(">", [one_plus_x, one])
	const one_plus_x_gt_zero := P(">", [one_plus_x, zero])
	const sequent_page_108 := ([x_plus_one_eq_one_plus_x, IMPLIES(x_plus_one_gt_one, x_plus_one_gt_zero)], IMPLIES(one_plus_x_gt_one, one_plus_x_gt_zero))
	const x' := "x'"
	const x_gt_one := P(">", [VAR(x'), one])
	const x_gt_zero := P(">", [VAR(x'), zero])

	type Sequent = (seq<Formula>, Formula)

	ghost predicate ValidSequent(s: Sequent) { forall p | p in s.0 || p == s.1 :: ValidFormula(p) }

	method PrintSequent(s: Sequent)
		requires ValidSequent(s)
	{
		if |s.0| > 0 {
			print FormulaToString(s.0[0]);
			var i := 1;
			while i < |s.0|
				invariant 1 <= i <= |s.0|
			{
				print ", ", FormulaToString(s.0[i]);
				i := i + 1;
			}
			print " ";
		}
		print "|- ", FormulaToString(s.1), "\n";
	}

	function Sequent_2_6(t1: Term, t2: Term): Sequent
		requires ValidTerm(t1)
		requires ValidTerm(t2)
	{
		([P("=", [t1, t2])], P("=", [t2, t1]))
	}

	method Main() {
		if !ValidFormula(f_2_1) { return; }
		print "The formula from Figure 2.1: ", FormulaToString(f_2_1), "\n";

		if !ValidFormula(f_page_102) { return; }
		print "\nA formula from page 102: ", FormulaToString(f_page_102), "\n";

		if !ValidFormula(f_2_2) { return; }
		print "\nThe formula from Figure 2.2: ", FormulaToString(f_2_2), "\n";

		print "\nThe sequent from page 108: ";
		if !ValidFormula(sequent_page_108.0[0]) { return; }
		if !ValidFormula(sequent_page_108.0[1]) { return; }
		if !ValidFormula(sequent_page_108.1) { return; }
		assert ValidSequent(sequent_page_108);
		PrintSequent(sequent_page_108);

		var t1, t2 := VAR("y"), VAR("z");
		assert VariablesInTerms([t1,t2]) == VariablesInTerm(t1) + VariablesInTerms([t2]) == {"y"} + VariablesInTerms([t2]) == {"y"} + {"z"} == {"y", "z"};
		var sequent_2_6 := Sequent_2_6(t1, t2);
		print "\nThe sequent from Example 2.6: ";
		PrintSequent(sequent_2_6);
		print "\n";
	}
}