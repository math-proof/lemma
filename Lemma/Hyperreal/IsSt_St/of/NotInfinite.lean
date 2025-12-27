import sympy.Basic
import Mathlib.Analysis.Real.Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite) :
-- imply
  x.IsSt x.st :=
-- proof
  Hyperreal.isSt_st' h


-- created on 2025-12-27
