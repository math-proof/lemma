import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n t : ℕ}
  {x y : ℕ → ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : t < n)
  (h : ∀ i, y i = if i < t then x i else x (i + 1)) :
-- imply
  ∑ i < (n - 1), f (y i) = ∑ i < n, f (x i) - f (x t) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = t + 1 + m := ⟨n - t - 1, by omega⟩
  rw [show t + 1 + m - 1 = t + m by omega]
  simp only [Nat.Iio_eq_range]
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_succ]
  have e1 : ∑ i < t, f (y i) = ∑ i < t, f (x i) :=
    Finset.sum_congr rfl (fun i hi => by rw [h i, ite_eq_left (by simpa using hi)])
  have e2 : ∑ k < m, f (y (t + k)) = ∑ k < m, f (x (t + 1 + k)) :=
    Finset.sum_congr rfl (fun k _ => by rw [h (t + k), ite_eq_right (by omega), show t + k + 1 = t + 1 + k by ring])
  simp only [Nat.Iio_eq_range] at e1 e2
  rw [e1, e2]
  ring


-- created on 2019-11-27
