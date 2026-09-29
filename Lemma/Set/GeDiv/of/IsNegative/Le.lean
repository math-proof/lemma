import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x g h : ℝ}
-- given
  (h₀ : x ∈ Set.Iio 0)
  (h₁ : g ≤ h) :
-- imply
  g / x ≥ h / x := by
-- proof
  exact (div_le_div_right_of_neg (Set.mem_Iio.mp h₀)).mpr h₁


-- created on 2026-09-27
