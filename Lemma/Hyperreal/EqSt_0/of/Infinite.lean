import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main, mt]
private lemma main
  {x : ℝ*}
-- given
  (h : x.Infinite) :
-- imply
  x.st = 0 :=
-- proof
  h.st_eq


-- created on 2025-12-12
