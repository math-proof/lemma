import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma induct
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (_h₀ : n ≥ 2)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range (n + 1)).map x) = H x (n + 1) / K x (n + 1) := by
-- proof
  exact alpha_eq x h n


-- created on 2026-09-27
