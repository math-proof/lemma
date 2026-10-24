import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.toFormal_zero](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions} :
-- imply
  ((0:Scalar d):Formal) = 0 :=
-- proof
  UnitsSystem.Scalar.toFormal_zero


-- created on 2026-10-22
