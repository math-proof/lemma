import Mathlib.Analysis.Complex.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma square_completing
  {a b c x : ℂ}
-- given
  (h : a ≠ 0) :
-- imply
  a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
-- proof
  field_simp
  ring


@[path]
private lemma square_completing.harmonic_mean
  {a b x y z : ℂ}
-- given
  (h : a + b ≠ 0) :
-- imply
  a * (x - y) ^ 2 + b * (x - z) ^ 2 = (a + b) * (x - (a * y + b * z) / (a + b)) ^ 2 + a * b / (a + b) * (y - z) ^ 2 := by
-- proof
  field_simp
  ring


-- created on 2026-09-27
