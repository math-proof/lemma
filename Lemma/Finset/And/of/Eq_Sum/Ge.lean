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
  (h₂ : ∀ i, x i ≥ 0) :
-- imply
  x n = a ∧ ∀ i < n, x i = 0 := by
-- proof
  rw [Nat.Iio_eq_range, Finset.sum_range_succ] at h₀
  simp only [← Nat.Iio_eq_range] at h₀
  have hS : ∑ i < n, x i ≥ 0 := Finset.sum_nonneg fun i _ => h₂ i
  have hS0 : ∑ i < n, x i = 0 := by linarith
  refine ⟨by linarith, fun i hi => ?_⟩
  have hle : x i ≤ ∑ i < n, x i := Finset.single_le_sum (fun j _ => h₂ j) (Finset.mem_Iio.mpr hi)
  linarith [h₂ i]


-- created on 2019-04-28
