import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
  -- given
  (h : x ≠ y)
  -- imply
  : x > y ∨ x < y := by
  -- proof
  have h' := lt_or_gt_of_ne h
  cases h' with
  | inl hlt => exact Or.inr hlt
  | inr hgt => exact Or.inl hgt

-- created on 2019-11-26
