import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x a b : ℤ}
  -- given
  (hlt : x < 0)
  (heq : a = b)
  -- imply
  : x < 0 ∧ a * x = b * x := by
  -- proof
  exact ⟨hlt, by rw [heq]⟩

-- created on 2023-03-26
-- updated on 2025-04-20
