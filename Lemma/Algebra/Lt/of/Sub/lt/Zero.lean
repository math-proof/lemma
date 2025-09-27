import Lemma.Algebra.LtAddS.is.Lt
open Algebra


/--
This lemma states that in an ordered additive commutative group, if the difference between two elements `x` and `y` is less than zero (i.e., `x - y < 0`), then `x` is strictly less than `y`.
The proof utilizes properties of ordered groups and algebraic manipulation to derive the inequality directly from the given hypothesis.
-/
@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x - y < 0) :
-- imply
  x < y := by
-- proof
  have := LtAddS.of.Lt y h
  simp at this
  assumption


-- created on 2025-03-24
-- updated on 2025-04-04
