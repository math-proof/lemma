import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (ha : 0 < a)
  (h : x ∈ Set.Icc a b) :
-- imply
  Real.log x ∈ Set.Icc (Real.log a) (Real.log b) := by
-- proof
  obtain ⟨hax, hxb⟩ := h
  have hx : 0 < x := lt_of_lt_of_le ha hax
  exact ⟨Real.log_le_log ha hax, Real.log_le_log hx hxb⟩


-- created on 2021-03-05
