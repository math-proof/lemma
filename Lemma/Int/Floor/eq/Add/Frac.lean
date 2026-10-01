import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  (⌊x⌋ : ℝ) = x - Int.fract x := by
-- proof
  exact (Int.self_sub_fract x).symm


-- created on 2026-09-27
