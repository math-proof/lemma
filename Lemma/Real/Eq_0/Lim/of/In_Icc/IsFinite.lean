import Mathlib.Analysis.SpecificLimits.Basic
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
open Filter Topology


@[main]
private lemma main
  {γ : ℝ}
  {x : ℕ → ℝ}
-- given
  (h₀ : γ ∈ Ioo 0 1)
  (h₁ : BddAbove (Set.range fun n => |x n|)) :
-- imply
  lim [n → ∞] γ ^ n * x n = 0 := by
-- proof
  obtain ⟨M, hM⟩ := h₁
  have h₂ : ∀ n, |x n| ≤ M := fun n => hM ⟨n, rfl⟩
  have h₃ : ∀ n, γ ^ n > 0 := fun n => pow_pos h₀.1 n
  have h₄ : ∀ n, |γ ^ n * x n| ≤ γ ^ n * M := by
    intro n
    rw [abs_mul, abs_of_pos (h₃ n)]
    exact mul_le_mul_of_nonneg_left (h₂ n) (h₃ n).le
  have h₅ : lim [n → ∞] γ ^ n * M = 0 := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h₀.1.le h₀.2).mul_const M
  exact squeeze_zero_norm h₄ h₅


-- created on 2026-09-26
