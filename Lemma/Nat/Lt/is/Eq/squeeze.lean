import Mathlib.Data.Int.Basic
import sympy.Basic


@[path]
private lemma main
  {x a : ℤ}
  -- imply
  : x < a ∧ a - 1 ≤ x ↔ x = a - 1 := by
  -- proof
  constructor
  · rintro ⟨h1, h2⟩
    omega
  · intro h
    constructor <;> omega

-- created on 2021-01-15
