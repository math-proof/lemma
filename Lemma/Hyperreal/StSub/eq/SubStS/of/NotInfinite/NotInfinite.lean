import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (h_a : ¬Hyperreal.Infinite x)
  (h_b : ¬Hyperreal.Infinite y) :
-- imply
  (x - y).st = x.st - y.st := by
-- proof
  sorry


-- created on 2025-12-10
