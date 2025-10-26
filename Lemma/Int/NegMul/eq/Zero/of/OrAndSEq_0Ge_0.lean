import Lemma.Int.Mul.eq.Zero.of.OrAndSEq_0Ge_0
import Lemma.Int.EqNeg_0.of.Eq_0
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : x = 0 ∧ y ≥ 0 ∨ y = 0 ∧ x ≥ 0) :
-- imply
  -(x * y) = 0 := by
-- proof
  have := Mul.eq.Zero.of.OrAndSEq_0Ge_0 h
  apply EqNeg_0.of.Eq_0 this


-- created on 2025-04-19
