import Mathlib.Analysis.SpecificLimits.Normed
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {γ : ℝ}
  {f : ℕ → ℝ}
-- given
  (h₀ : γ ∈ Set.Ioo (-1) 1)
  (h₁ : ∃ M, ∀ k, |f k| ≤ M) :
-- imply
  Summable (fun k : ℕ => γ ^ k * f k) := by
-- proof
  have hγ : |γ| < 1 := by
    rwa [abs_lt]
  obtain ⟨M, hM⟩ := h₁
  refine Summable.of_norm_bounded (g := fun k => M * |γ| ^ k)
    ((summable_geometric_of_lt_one (abs_nonneg _) hγ).mul_left M) ?_
  intro k
  calc
    _ = |γ| ^ k * |f k| := by simp [norm_mul, norm_pow, Real.norm_eq_abs]
    _ ≤ |γ| ^ k * M := mul_le_mul_of_nonneg_left (hM k) (pow_nonneg (abs_nonneg _) _)
    _ = M * |γ| ^ k := mul_comm _ _


-- created on 2023-04-16
-- updated on 2026-10-26
