import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  (x⁻¹).st = x.st⁻¹ :=
-- proof
  Hyperreal.st_inv x


-- created on 2025-12-09
-- updated on 2025-12-10
