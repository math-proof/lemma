import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.coe_neg](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {r:ℝ} :
-- imply
  ((-r:ℝ):Scalar 0) = -(r:Scalar 0) :=
-- proof
  UnitsSystem.Scalar.coe_neg r


-- created on 2026-10-22
