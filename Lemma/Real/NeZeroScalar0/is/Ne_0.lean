import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.neZero_coe_iff](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {r:ℝ} :
-- imply
  NeZero (r:Scalar 0) ↔ r ≠ 0 :=
-- proof
  UnitsSystem.Scalar.neZero_coe_iff


-- created on 2026-10-22
