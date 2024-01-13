/* Tutorial 8: total order + functions */

module Tutorial08 {
/*
Given the sets

A={1,2,3}, R1={(1,1), (2,2), (2,3), (3,3)}

The union of R1 with which of the following sets represents a total order on A?

{(2,1), (3,1)} // YES! the order is 2 "<" 3 "<" 1 
{(1,2), (1,3), (2,1), (3,1), (3,2)} // NO, due to (3,2) the union is not anti-symmtric
{(1,2), (3,1)} // NO, missing (1,3) for transitivity
{(1,2)} // NO, missing (1,3) for transitivity

Which of the following sets represents an injective function from the set {4,5,6} to {4,5,6,7}?

{(4,4), (5,5), (6,7)}         // YES! (It is not surjective onto {4,5,6,7})
{(4,4), (4,5), (5,6), (6,7)}  // NO, not a valid function due to the two "exits" from 4
{(4,4), (5,4), (6,4)}         // NO, this is not an injective function, due to 4 in the range, being the range/image of 3 domain elements
{}                            // NO, not a function from the set {4,5,6} due to Domain({}) == {}

Which of the following sets represents an surjective function from the set {1,2,3} to {1,2,3,4}?

{(1,1), (2,1), (3,3), (4,2)}  // YES (even though this function is not injective, which is fine, not all functions must be injective)
{(1,3), (2,2), (3,1), (4,0)}  // NO, 0 is not allowed in the range of this function: !(Range(F) <= iset{1,2,3}): 0 !in iset{1,2,3}
{(1,1), (2,2), (3,3)}         // NO, 4 !in Domain(F), so !(Domain(F) == iset{1,2,3,4})
{(1,1), (1,2), (1,3)}         // NO, it seems to be surjective (Range(F) == iset{1,2,3}) but it is NOT a valid function (1,1),(1,2); furthermore, Domain(F) is iset{1}, missing pairs for 2,3 and 4

*/
    method M8() {}
}