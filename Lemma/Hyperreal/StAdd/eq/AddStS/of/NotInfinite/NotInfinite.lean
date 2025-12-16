import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (h_a : ¬x.Infinite)
  (h_b : ¬y.Infinite) :
-- imply
  (x + y).st = x.st + y.st :=
-- proof
  Hyperreal.st_add h_a h_b


-- created on 2025-12-10
