import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x g h : ℝ}
-- given
  (h₀ : x ∈ Set.Ioi 0)
  (h₁ : g ≤ h) :
-- imply
  g / x ≤ h / x := by
-- proof
  exact (div_le_div_iff_of_pos_right (Set.mem_Ioi.mp h₀)).mpr h₁


-- created on 2026-09-27
