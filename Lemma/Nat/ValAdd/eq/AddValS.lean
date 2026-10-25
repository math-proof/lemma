import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_add](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q₁ q₂:Scalar d} :
-- imply
  (q₁ + q₂).val = q₁.val + q₂.val :=
-- proof
  UnitsSystem.Scalar.val_add q₁ q₂


-- created on 2026-10-22
