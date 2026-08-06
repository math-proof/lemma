import Lemma.Nat.Eq_0.of.EqAddSquareS0
open Nat


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
  [NoZeroDivisors α] [NeZero (1 : α)]
  {x y : α}
-- given
  (h : x² + y² = 0) :
-- imply
  x = 0 ∧ y = 0 := by
-- proof
  refine ⟨Eq_0.of.EqAddSquareS0 h, ?_⟩
  rw [add_comm] at h
  exact Eq_0.of.EqAddSquareS0 h


-- created on 2018-06-09
