import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.coe_sub](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {r s:ℝ} :
-- imply
  ((r-s:ℝ):Scalar 0) = (r:Scalar 0) - (s:Scalar 0) :=
-- proof
  UnitsSystem.Scalar.coe_sub r s


-- created on 2026-10-22
