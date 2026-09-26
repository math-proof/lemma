import sympy.Basic
import sympy.stats.stochastic_process_types


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {μ : S → ℝ}
  {P : Matrix S S ℝ}
-- given
  (h₀ : RowStochastic P)
  (h₁ : StochasticVec μ) :
-- imply
  ∑ i, ∑ j, μ i * P i j = 1 := by
-- proof
  calc
    _ = ∑ i, μ i * ∑ j, P i j := by
      simp [Finset.mul_sum]
    _ = ∑ i, μ i := by
      simp [fun i => (h₀.stochastic i).rowsum]
    _ = 1 := h₁.rowsum


-- created on 2026-09-19
-- updated on 2026-09-26
