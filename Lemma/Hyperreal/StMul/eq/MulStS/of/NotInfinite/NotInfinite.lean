import sympy.Basic
import Mathlib.Analysis.Real.Hyperreal


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (hx : ¬Hyperreal.Infinite x)
  (hy : ¬Hyperreal.Infinite y) :
-- imply
  (x * y).st = x.st * y.st :=
-- proof
  Hyperreal.st_mul hx hy


-- created on 2025-12-10
