import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Misc.UnitsSystem.Part23
open UnitsSystem
open UnitsSystem.Scalar


/--
[Scalar.val_hMul](https://github.com/teorth/analysis/blob/main/Analysis/Misc/UnitsSystem.lean)
-/
@[path]
private lemma main
  [UnitsSystem]
  {d₁ d₂:Dimensions}
  {q₁:Scalar d₁}
  {q₂:Scalar d₂} :
-- imply
  (q₁ * q₂).val = q₁.val * q₂.val :=
-- proof
  UnitsSystem.Scalar.val_hMul q₁ q₂


-- created on 2026-10-22
