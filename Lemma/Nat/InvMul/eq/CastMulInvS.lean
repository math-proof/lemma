import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.mul_inv](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d₁ d₂:Dimensions}
  {q₁:Scalar d₁}
  {q₂:Scalar d₂} :
-- imply
  (q₁ * q₂).inv = ((q₁.inv) * (q₂.inv)).cast :=
-- proof
  UnitsSystem.Scalar.mul_inv q₁ q₂


-- created on 2026-10-22
