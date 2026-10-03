import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e a b : ℝ}
-- given
  (h : e ∉ Ico a b) :
-- imply
  e < a ∨ e ≥ b := by
-- proof
  rw [Set.mem_Ico, not_and_or] at h
  obtain h | h := h
  · exact Or.inl (not_le.mp h)
  · exact Or.inr (not_lt.mp h)


-- created on 2019-07-08
