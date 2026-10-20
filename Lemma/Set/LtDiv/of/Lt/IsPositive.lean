import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a < b)
  (h₁ : x ∈ Set.Ioi 0) :
-- imply
  a / x < b / x := by
-- proof
  rw [Set.mem_Ioi] at h₁
  exact div_lt_div_of_pos_right h₀ h₁


-- created on 2021-10-02
-- updated on 2026-10-17
