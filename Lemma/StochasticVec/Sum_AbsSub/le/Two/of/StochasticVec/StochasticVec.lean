import sympy.stats.generator_matrix
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {μ ν : S → ℝ}
-- given
  (h₀ : StochasticVec μ)
  (h₁ : StochasticVec ν) :
-- imply
  ∑ i, |μ i - ν i| ≤ 2 := by
-- proof
  calc
    _ ≤ ∑ i, (μ i + ν i) :=
      Finset.sum_le_sum fun i _ => abs_sub_le_iff.2 ⟨by linarith [h₀.nonneg i, h₁.nonneg i], by linarith [h₀.nonneg i, h₁.nonneg i]⟩
    _ = 2 := by
      rw [Finset.sum_add_distrib, h₀.rowsum, h₁.rowsum]
      norm_num


-- created on 2026-09-26
