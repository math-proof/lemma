import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b d : ℤ}
-- given
  (h : x ∉ Set.Ico a b)
  (hd : d > 0) :
-- imply
  d * x ∉ Set.Ico (a * d) ((b - 1) * d + 1) := by
-- proof
  intro hmem
  obtain ⟨h₁, h₂⟩ := hmem
  rw [mul_comm a d] at h₁
  have hle := (mul_le_mul_iff_right₀ hd).mp h₁
  rw [Int.lt_add_one_iff, mul_comm (b - 1) d] at h₂
  have hlt := (mul_le_mul_iff_right₀ hd).mp h₂
  exact h ⟨hle, by omega⟩


-- created on 2021-06-08
