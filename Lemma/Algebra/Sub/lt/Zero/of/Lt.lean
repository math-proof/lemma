import Lemma.Algebra.LtSubS.of.Lt
import Lemma.Algebra.Sub.eq.Zero
open Algebra


/--
In an ordered additive commutative group, if an element `x` is less than another element `y`, then the difference `x - y` is negative.
This lemma leverages the order-preserving property of subtraction and the inverse element axiom to establish that `x - y < 0` under the given condition.
-/
@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x - y < 0 := by
-- proof
  have := LtSubS.of.Lt h y
  rw [Sub.eq.Zero] at this
  assumption


-- created on 2025-03-15
-- updated on 2025-04-04
