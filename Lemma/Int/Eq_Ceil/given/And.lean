import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {y : ℤ}
-- given
  (h : (y : ℝ) = Int.ceil x) :
-- imply
  x ≤ (y : ℝ) ∧ (y : ℝ) < x + 1 := by
-- proof
  have h1 : x ≤ Int.ceil x := Int.le_ceil x
  have h2 : (Int.ceil x : ℝ) < x + 1 := Int.ceil_lt_add_one x
  rw [← h] at *
  exact ⟨h1, h2⟩


-- created on 2019-03-08
