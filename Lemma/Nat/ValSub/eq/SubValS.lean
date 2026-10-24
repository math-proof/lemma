import Mathlib
import sympy.Basic
import sympy.analysis.Misc.UnitsSystem
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_sub](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q₁ q₂ : Scalar d} :
-- imply
  (q₁ - q₂).val = q₁.val - q₂.val :=
-- proof
  UnitsSystem.Scalar.val_sub q₁ q₂


-- created on 2026-10-22
