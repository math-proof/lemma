import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.in_inj](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {unit q₁ q₂:Scalar d} [h: NeZero unit] :
-- imply
  unit.in q₁ = unit.in q₂ ↔ q₁ = q₂ :=
-- proof
  UnitsSystem.Scalar.in_inj unit q₁ q₂


-- created on 2026-10-22
