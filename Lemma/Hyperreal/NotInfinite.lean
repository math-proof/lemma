import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
-- given
  (r : ℝ) :
-- imply
  ¬Hyperreal.Infinite r :=
-- proof
  Hyperreal.not_infinite_real r


-- created on 2025-12-11
