import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n ≥ 2)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range n).map x).reverse = H x n / H x (n - 1) := by
-- proof
  have key : ∀ m, alpha ((List.range (m + 1)).map x).reverse = H x (m + 1) / H x m := by
    intro m
    induction m with
    | zero => simp [alpha, H]
    | succ m ih =>
      rw [List.range_succ (n := m + 1), List.map_append, List.reverse_append, List.map_singleton, List.reverse_singleton,
        List.singleton_append, alpha_cons _ (by simp), ih]
      have h2 : H x (m + 1) ≠ 0 := (H_pos x h (m + 1)).ne'
      show x (m + 1) + 1 / (H x (m + 1) / H x m) = (H x (m + 1) * x (m + 1) + H x m) / H x (m + 1)
      rw [one_div_div, add_div' _ _ _ h2]
      ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact key m


-- created on 2026-09-27
