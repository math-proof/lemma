import sympy.concrete.continuant_shift
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, 1 ≤ i → i < n → x i > 0) :
-- imply
  K x n > 0 := by
-- proof
  exact K_pos_of x n h₀ h


-- created on 2026-09-27
