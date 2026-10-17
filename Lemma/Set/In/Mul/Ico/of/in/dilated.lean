import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {e a b d : ℤ}
-- given
  (h₀ : e ∈ Finset.Ico a b)
  (h₁ : d > 0) :
-- imply
  e * d ∈ Finset.Ico (a * d) ((b - 1) * d + 1) := by
-- proof
  rw [Finset.mem_Ico] at h₀ ⊢
  refine ⟨?_, ?_⟩
  ·
    exact Int.mul_le_mul_of_nonneg_right h₀.1 (by omega)
  ·
    have he : e ≤ b - 1 := by omega
    have hmul : e * d ≤ (b - 1) * d := Int.mul_le_mul_of_nonneg_right he (by omega)
    omega


-- created on 2026-10-11
-- updated on 2026-10-17
