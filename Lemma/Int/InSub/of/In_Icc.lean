import Mathlib.Order.Interval.Set.Basic
import sympy.Basic


@[main]
private lemma main
  {e a b t : ℝ}
-- given
  (h : e ∈ Set.Icc a b) :
-- imply
  e - t ∈ Set.Icc (a - t) (b - t) := by
-- proof
  exact ⟨sub_le_sub h.1 le_rfl, sub_le_sub h.2 le_rfl⟩


-- created on 2018-04-08
