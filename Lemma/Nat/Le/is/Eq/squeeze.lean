import Mathlib.Data.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
  -- imply
  : a ≤ b ∧ b ≤ a ↔ a = b := by
  -- proof
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 h2
  · intro h
    exact ⟨le_of_eq h, le_of_eq h.symm⟩

-- created on 2019-05-30
