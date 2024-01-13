/*

DeMorgan 2: negation of conjunction is the disjunction of the negations

!(P && Q) == !P || !Q

We need to check that the 4th column is equal to the 7th column:

 P  Q  (P && Q)  !(P && Q)  !P     !Q    (!P || !Q)
 F  F  F         T          T      T     T   
 F  T  F         T          T      F     T
 T  F  F         T          F      T     T
 T  T  T         F          F      F     F

Intro to Dafny:
*/

const T := true
const F := false

lemma DeMorgan2(P: bool, Q: bool)
	ensures !(P && Q) == !P || !Q
{}
