import sympy.sets.sets
import sympy.Basic


@[main]
private lemma squeeze
  {n : ℕ}
  {x : ℕ → ℝ}
  {a : ℝ}
-- given
  (h₀ : ∑ i ∈ Finset.range (n + 1), x i = a)
  (h₁ : x n ≥ a)
  (h₂ : ∀ i < n + 1, x i ≥ 0) :
-- imply
  x n = a ∧ ∀ i < n, x i = 0 := by
-- proof
  rw [Finset.sum_range_succ] at h₀
  have hnn : ∀ j ∈ Finset.range n, 0 ≤ x j := fun j hj => h₂ j (by rw [Finset.mem_range] at hj; omega)
  have hS : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg hnn
  have hS0 : ∑ i ∈ Finset.range n, x i = 0 := by linarith
  refine ⟨by linarith, fun i hi => ?_⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS0 i (Finset.mem_range.mpr hi)


-- created on 2019-04-27
