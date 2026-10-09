import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {a b : ℝ}
  {w x : ℕ → ℝ}
-- given
  (h₀ : ∑ i ∈ Finset.range n, w i = 1)
  (h₁ : ∀ i ∈ Finset.range n, 0 ≤ w i ∧ x i ∈ Set.Icc a b) :
-- imply
  ∑ i ∈ Finset.range n, w i * x i ∈ Set.Icc a b := by
-- proof
  apply Set.mem_Icc.mpr
  constructor
  · calc
      _ = ∑ i ∈ Finset.range n, w i * a := by rw [← Finset.sum_mul, h₀, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (h₁ i hi).2.1 (h₁ i hi).1
  · calc
      _ ≤ ∑ i ∈ Finset.range n, w i * b := Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (h₁ i hi).2.2 (h₁ i hi).1
      _ = b := by rw [← Finset.sum_mul, h₀, one_mul]


-- created on 2020-05-31
-- updated on 2023-05-21
