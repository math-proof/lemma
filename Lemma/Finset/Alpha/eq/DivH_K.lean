import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma positive
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range n).map x) = H x n / K x n := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact alpha_eq x h m


-- created on 2026-09-27
