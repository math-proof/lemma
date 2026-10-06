import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (hgt : 0 < x)
  (heq : a = b)
  -- imply
  : 0 < x ∧ a * x = b * x := by
  -- proof
  exact ⟨hgt, by rw [heq]⟩

-- created on 2023-03-26
