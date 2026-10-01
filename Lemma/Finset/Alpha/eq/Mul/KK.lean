import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range n).map fun i => x (i + 1)).reverse = K x (n + 1) / K x n := by
-- proof
  have key : ∀ m, alpha ((List.range (m + 1)).map fun i => x (i + 1)).reverse = K x (m + 1 + 1) / K x (m + 1) := by
    intro m
    induction m with
    | zero => simp [alpha, K]
    | succ m ih =>
      rw [List.range_succ (n := m + 1), List.map_append, List.reverse_append, List.map_singleton, List.reverse_singleton,
        List.singleton_append, alpha_cons _ (by simp), ih]
      have h2 : K x (m + 1 + 1) ≠ 0 := (K_nonneg_pos x h (m + 1)).2.ne'
      show x (m + 1 + 1) + 1 / (K x (m + 1 + 1) / K x (m + 1)) =
        (K x (m + 1 + 1) * x (m + 1 + 1) + K x (m + 1)) / K x (m + 1 + 1)
      rw [one_div_div, add_div' _ _ _ h2]
      ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m


-- created on 2020-09-27
