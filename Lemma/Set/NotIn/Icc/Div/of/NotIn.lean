import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b d : ℝ}
-- given
  (h : x ∉ Set.Icc a b)
  (hd : d > 0) :
-- imply
  x / d ∉ Set.Icc (a / d) (b / d) := by
-- proof
  intro hmem
  obtain ⟨h₁, h₂⟩ := hmem
  rw [le_div_iff₀ hd, div_mul_cancel₀ _ hd.ne'] at h₁
  rw [div_le_iff₀ hd, div_mul_cancel₀ _ hd.ne'] at h₂
  exact h ⟨h₁, h₂⟩


-- created on 2021-06-07
