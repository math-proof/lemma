import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n t : ℕ}
  {x y : ℕ → ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : t < n)
  (h : ∀ i, y i = if i < t then x i else x (i + 1)) :
-- imply
  ∑ i ∈ Finset.range (n - 1), f (y i) = ∑ i ∈ Finset.range n, f (x i) - f (x t) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = t + 1 + m := ⟨n - t - 1, by omega⟩
  rw [show t + 1 + m - 1 = t + m by omega, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_succ]
  have e1 : ∑ i ∈ Finset.range t, f (y i) = ∑ i ∈ Finset.range t, f (x i) :=
    Finset.sum_congr rfl (fun i hi => by rw [h i, if_pos (Finset.mem_range.mp hi)])
  have e2 : ∑ k ∈ Finset.range m, f (y (t + k)) = ∑ k ∈ Finset.range m, f (x (t + 1 + k)) :=
    Finset.sum_congr rfl (fun k _ => by rw [h (t + k), if_neg (by omega), show t + k + 1 = t + 1 + k by ring])
  rw [e1, e2]
  ring


-- created on 2026-09-27
