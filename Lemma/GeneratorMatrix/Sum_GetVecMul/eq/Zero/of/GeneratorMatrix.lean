import sympy.stats.generator_matrix
import sympy.Basic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {Q : Matrix S S ℝ}
-- given
  (h₀ : GeneratorMatrix Q)
  (ξ : S → ℝ) :
-- imply
  ∑ i, (ξ ᵥ* Q) i = 0 := by
-- proof
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, h₀.rowsum]


-- created on 2026-09-26
