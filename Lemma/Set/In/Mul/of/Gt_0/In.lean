import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {t x a b : ℝ}
-- given
  (h₀ : t > 0)
  (h₁ : x ∈ Set.Icc a b) :
-- imply
  x * t ∈ Set.Icc (a * t) (b * t) := by
-- proof
  exact ⟨mul_le_mul_of_nonneg_right h₁.1 h₀.le, mul_le_mul_of_nonneg_right h₁.2 h₀.le⟩


@[main]
private lemma left_open
  {t x a b : ℝ}
-- given
  (h₀ : t > 0)
  (h₁ : x ∈ Set.Ioc a b) :
-- imply
  x * t ∈ Set.Ioc (a * t) (b * t) := by
-- proof
  exact ⟨mul_lt_mul_of_pos_right h₁.1 h₀, mul_le_mul_of_nonneg_right h₁.2 h₀.le⟩


-- created on 2026-09-27
