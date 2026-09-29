import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (hn : n > 0) :
-- imply
  ∑ i ∈ Finset.range n, (x i - (∑ j ∈ Finset.range n, x j) / n) ^ 2 = (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i - x j) ^ 2) / n := by
-- proof
  have e1 : ∀ (m : ℕ) (a : ℝ), ∑ j ∈ Finset.range m, (a - x j) ^ 2 = m * a ^ 2 - 2 * a * ∑ j ∈ Finset.range m, x j + ∑ j ∈ Finset.range m, x j ^ 2 := by
    intro m a
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      push_cast
      ring
  have e2 : ∀ (m : ℕ) (a : ℝ), ∑ j ∈ Finset.range m, (x j - a) ^ 2 = m * a ^ 2 - 2 * a * ∑ j ∈ Finset.range m, x j + ∑ j ∈ Finset.range m, x j ^ 2 := by
    intro m a
    rw [← e1]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have key : ∀ m : ℕ, ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i, (x i - x j) ^ 2 = m * ∑ i ∈ Finset.range m, x i ^ 2 - (∑ i ∈ Finset.range m, x i) ^ 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      rw [ih, e1]
      push_cast
      ring
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [e2, key]
  field_simp
  ring


-- created on 2026-09-27
