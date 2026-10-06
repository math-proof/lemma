import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
  -- given
  (h : x ≤ max a b)
  -- imply
  : x ≤ a ∨ x ≤ b := by
  -- proof
  cases' le_total a b with h' h'
  · have hm : max a b = b := by simp [h']
    rw [hm] at h
    exact Or.inr h
  · have hm : max a b = a := by simp [h']
    rw [hm] at h
    exact Or.inl h

-- created on 2022-01-01
