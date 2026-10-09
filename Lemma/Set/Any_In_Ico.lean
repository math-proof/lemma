import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  ∃ k : ℤ, x ∈ Set.Ico (k : ℝ) (k + 1) := by
-- proof
  exact ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩


-- created on 2019-12-04
