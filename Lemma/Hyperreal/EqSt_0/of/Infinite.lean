import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Hyperreal.Infinite x) :
-- imply
  x.st = 0 :=
-- proof
  h.st_eq


-- created on 2025-12-12
