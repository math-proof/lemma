import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.StandardUnit


/--
[StandardUnit.mul](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d₁ d₂:Dimensions} :
-- imply
  StandardUnit d₁ * StandardUnit d₂ = StandardUnit (d₁+d₂) :=
-- proof
  UnitsSystem.StandardUnit.mul d₁ d₂


-- created on 2026-10-22
