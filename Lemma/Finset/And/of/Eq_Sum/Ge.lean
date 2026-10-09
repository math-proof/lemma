import sympy.sets.sets
import sympy.Basic


@[path]
private lemma squeeze
  {n : ℕ}
  {x : ℕ → ℝ}
  {a : ℝ}
-- given
  (h₀ : ∑ i ∈ Finset.range (n + 1), x i = a)
  (h₁ : x n ≥ a)
  (h₂ : ∀ i, x i ≥ 0) :
-- imply
  x n = a ∧ ∀ i ∈ Finset.range n, x i = 0 := by
-- proof
  rw [Finset.sum_range_succ] at h₀
  have hS : ∑ i ∈ Finset.range n, x i ≥ 0 := Finset.sum_nonneg fun i _ => h₂ i
  have hS0 : ∑ i ∈ Finset.range n, x i = 0 := by linarith
  refine ⟨by linarith, fun i hi => ?_⟩
  have hle : x i ≤ ∑ i ∈ Finset.range n, x i := Finset.single_le_sum (fun j _ => h₂ j) hi
  linarith [h₂ i]


-- created on 2019-04-28
