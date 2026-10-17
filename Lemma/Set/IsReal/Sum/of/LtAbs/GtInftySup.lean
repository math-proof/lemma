import Mathlib.Analysis.SpecificLimits.Normed
import sympy.Basic


@[path]
private lemma main
  {γ : ℝ}
  {f : ℕ → ℝ}
-- given
  (h₀ : |γ| < 1)
  (h₁ : ∃ M, ∀ k, |f k| ≤ M) :
-- imply
  Summable (fun k : ℕ => γ ^ k * f k) := by
-- proof
  obtain ⟨M, hM⟩ := h₁
  refine Summable.of_norm_bounded (g := fun k => M * |γ| ^ k)
    ((summable_geometric_of_lt_one (abs_nonneg _) h₀).mul_left M) ?_
  intro k
  calc
    _ = |γ| ^ k * |f k| := by simp [norm_mul, norm_pow, Real.norm_eq_abs]
    _ ≤ |γ| ^ k * M := mul_le_mul_of_nonneg_left (hM k) (pow_nonneg (abs_nonneg _) _)
    _ = M * |γ| ^ k := mul_comm _ _


-- created on 2026-10-11
-- updated on 2026-10-17
