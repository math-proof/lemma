import Lemma.Nat.LtAddS.is.Lt
import Lemma.Algebra.Sub.eq.Add_Neg
open Algebra Nat


/--
Given an ordered additive commutative group `α`, if `x < y` for elements `x, y : α`, then subtracting the same element `z : α` from both `x` and `y` preserves the inequality.
Specifically, `x - z < y - z`.
This follows by expressing subtraction as addition of the negation and applying the property that addition preserves strict order.
-/
@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x < y)
  (z : α) :
-- imply
  x - z < y - z := by
-- proof
  rw [Sub.eq.Add_Neg (a := x), Sub.eq.Add_Neg (a := y)]
  apply LtAddS.of.Lt _ h


-- created on 2024-07-01
-- updated on 2025-04-04
