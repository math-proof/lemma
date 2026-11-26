import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma squeeze
  {n : ℕ}
  {x : ℕ → ℝ}
  {a : ℝ}
-- given
  (h₀ : ∑ i < (n + 1), x i = a)
  (h₁ : x n ≥ a)
  (h₂ : ∀ i < n + 1, x i ≥ 0) :
-- imply
  x n = a ∧ ∀ i < n, x i = 0 := by
-- proof
  rw [Nat.Iio_eq_range] at h₀
  rw [Finset.sum_range_succ] at h₀
  rw [← Nat.Iio_eq_range] at h₀
  have hnn : ∀ j < n, 0 ≤ x j := fun j hj => h₂ j (by omega)
  have hS : 0 ≤ ∑ i < n, x i := Finset.sum_nonneg (fun j hj => hnn j (by simpa using hj))
  have hS0 : ∑ i < n, x i = 0 := by linarith
  refine ⟨by linarith, fun i hi => ?_⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hnn j (by simpa using hj))).mp hS0 i (by simpa using hi)


-- created on 2019-04-27
