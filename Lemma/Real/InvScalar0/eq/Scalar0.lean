import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.inv_coe](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {r:ℝ} :
-- imply
  ((r:Scalar 0).inv:Formal) = ((r⁻¹:ℝ):Scalar 0) :=
-- proof
  UnitsSystem.Scalar.inv_coe r


-- created on 2026-10-22
