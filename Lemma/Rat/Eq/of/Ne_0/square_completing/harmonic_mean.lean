import Mathlib.Data.Complex.Basic
import sympy.Basic


@[path]
private lemma main
  {a b x y z : ℂ}
  -- given
  (hab : a + b ≠ 0)
  -- imply
  : a * (x - y) ^ 2 + b * (x - z) ^ 2
    = (a + b) * (x - (a * y + b * z) / (a + b)) ^ 2 + (a * b / (a + b)) * (y - z) ^ 2 := by
  -- proof
  field_simp [hab]
  ring

-- created on 2023-04-10
