import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  (-x).st = -x.st :=
-- proof
  Hyperreal.st_neg x


-- created on 2025-12-16
