import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x : ℝ}
  {y : ℤ}
-- given
  (h₀ : x + 1 > y)
  (h₁ : y ≥ x) :
-- imply
  y = ⌈x⌉ := by
-- proof
  rw [eq_comm, Int.ceil_eq_iff]
  constructor <;> linarith


-- created on 2026-09-27
