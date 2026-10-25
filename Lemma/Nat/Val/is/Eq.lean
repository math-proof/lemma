import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_inj](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d:Dimensions}
  {q₁ q₂:Scalar d} :
-- imply
  q₁.val = q₂.val ↔ q₁ = q₂ :=
-- proof
  UnitsSystem.Scalar.val_inj q₁ q₂


-- created on 2026-10-22
