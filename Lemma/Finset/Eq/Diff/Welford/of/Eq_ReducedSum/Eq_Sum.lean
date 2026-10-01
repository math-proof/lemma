import Mathlib.Algebra.Group.ForwardDiff
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x xb : ℕ → ℝ}
  {M : ℕ → ℝ}
-- given
  (h₀ : ∀ n, xb n = (∑ k ∈ Finset.range n, x k) / n)
  (h₁ : ∀ n, M n ^ 2 = ∑ k ∈ Finset.range n, (x k - xb n) ^ 2) :
-- imply
  fwdDiff 1 (fun n => M n ^ 2) n = (x n - xb (n + 1)) * (x n - xb n) := by
-- proof
  have e : ∀ m c, ∑ k ∈ Finset.range m, (x k - c) ^ 2 =
      ∑ k ∈ Finset.range m, x k ^ 2 - 2 * c * ∑ k ∈ Finset.range m, x k + m * c ^ 2 := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      ring
  show M (n + 1) ^ 2 - M n ^ 2 = _
  rw [h₁ (n + 1), h₁ n, e, e, h₀ (n + 1), h₀ n]
  simp only [Finset.sum_range_succ]
  push_cast
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    ring
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring


@[main]
private lemma biased
  {n : ℕ}
  {x xb : ℕ → ℝ}
  {σ : ℕ → ℝ}
-- given
  (h₀ : ∀ n, xb n = (∑ k ∈ Finset.range n, x k) / n)
  (h₁ : ∀ n, σ n ^ 2 = (∑ k ∈ Finset.range n, (x k - xb n) ^ 2) / n) :
-- imply
  fwdDiff 1 (fun n => σ n ^ 2) n = ((x n - xb (n + 1)) * (x n - xb n) - σ n ^ 2) / (n + 1) := by
-- proof
  have e : ∀ m c, ∑ k ∈ Finset.range m, (x k - c) ^ 2 =
      ∑ k ∈ Finset.range m, x k ^ 2 - 2 * c * ∑ k ∈ Finset.range m, x k + m * c ^ 2 := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      ring
  show σ (n + 1) ^ 2 - σ n ^ 2 = _
  rw [h₁ (n + 1), h₁ n, e, e, h₀ (n + 1), h₀ n]
  simp only [Finset.sum_range_succ]
  push_cast
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    ring
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring


@[main]
private lemma unbiased
  {n : ℕ}
  {x xb : ℕ → ℝ}
  {s : ℕ → ℝ}
-- given
  (h₀ : ∀ n, xb n = (∑ k ∈ Finset.range n, x k) / n)
  (h₁ : ∀ n, s n ^ 2 = (∑ k ∈ Finset.range n, (x k - xb n) ^ 2) / ((n : ℝ) - 1))
  (h : n > 0) :
-- imply
  fwdDiff 1 (fun n => s n ^ 2) n = (x n - xb n) ^ 2 / (n + 1) - s n ^ 2 / n := by
-- proof
  have e : ∀ m c, ∑ k ∈ Finset.range m, (x k - c) ^ 2 =
      ∑ k ∈ Finset.range m, x k ^ 2 - 2 * c * ∑ k ∈ Finset.range m, x k + m * c ^ 2 := by
    intro m c
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      ring
  show s (n + 1) ^ 2 - s n ^ 2 = _
  rw [h₁ (n + 1), h₁ n, e, e, h₀ (n + 1), h₀ n]
  simp only [Finset.sum_range_succ]
  push_cast
  obtain rfl | hn : n = 1 ∨ n ≥ 2 := by omega
  · norm_num
    ring
  · generalize ∑ k ∈ Finset.range n, x k = S
    generalize ∑ k ∈ Finset.range n, x k ^ 2 = Q
    have h2 : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    generalize (n : ℝ) = N at h2 ⊢
    have hN : N ≠ 0 := by positivity
    have hN1 : N - 1 ≠ 0 := by linarith
    have hN2 : N + 1 ≠ 0 := by linarith
    rw [add_sub_cancel_right]
    field_simp
    ring


-- created on 2023-11-07
