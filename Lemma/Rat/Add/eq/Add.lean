import Mathlib.Analysis.Complex.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma square_completing
  {a b c x : ℂ}
-- given
  (ha : a ≠ 0) :
-- imply
  a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
-- proof
  field_simp
  ring


-- created on 2023-04-10
