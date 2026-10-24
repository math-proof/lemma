import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.in_smul](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {c:ℝ}
  {unit q:Scalar d} :
-- imply
  unit.in (c • q) = c * unit.in q :=
-- proof
  UnitsSystem.Scalar.in_smul c unit q


-- created on 2026-10-22
