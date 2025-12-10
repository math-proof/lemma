import sympy.Basic
import Mathlib.Analysis.Real.Hyperreal


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (h_a : ¬Hyperreal.Infinite x)
  (h_b : ¬Hyperreal.Infinite y) :
-- imply
  (x + y).st = x.st + y.st :=
-- proof
  Hyperreal.st_add h_a h_b


-- created on 2025-12-10
